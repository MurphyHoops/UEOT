"""Proper-clock weak volume/source inequality; archived FLRW and vacuum controls."""
from fractions import Fraction as F
import argparse
import json
from pathlib import Path
import sys

from mpmath import iv

BASE=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(BASE))
from finite_window import q, scalar, scale

PAIRS=((1,2,5,6),(2,3,6,7))
N=1024
END=F(1,4)


def clock_weight(eta):
    x=4*eta
    h=x*(1-x)
    w=256*h**4
    wx=1024*h**3*(1-2*x)
    wxx=3072*h**2*(1-2*x)**2-2048*h**3
    a=scale(eta)
    # w' = dw/dtau; k*deta = w''*dtau
    return w,4*wx/a,(16*wxx+4*wx*iv.tan(2*eta))/a


def gate(eta,cell,left,right):
    if cell<left:
        return q(0),q(0)
    if cell>=right:
        return q(1),q(0)
    t=(32*eta-left)/(right-left)
    return t**3*(10+t*(-15+6*t)),960*t**2*(1-t)**2/(right-left)


def readings(eta,cell):
    a=scale(eta)
    w,_,k=clock_weight(eta)
    cs=iv.cos(2*eta)
    y=3*iv.ln(cs)/2
    pi=1/(cs*iv.sqrt(cs))
    theta=-3*iv.tan(2*eta)/a
    out=[-k*y,2*w*pi**2*a,w*theta**2*a/3]
    for l,r,i,j in PAIRS:
        e,de=gate(eta,cell,l,r)
        f,df=gate(eta,cell,i,j)
        S=f-e
        out.extend([(df-de)*scalar(eta),-S*pi*a,S**2*a/w if l<=cell<j else q(0)])
    return out


def certified_integrals():
    # Five-point Gauss-Legendre rule, degree 9 exact, positive weights summing to 2.
    u=iv.sqrt(q("10/7"))
    nodes=[(q(0),q("128/225"))]
    for sign in (-1,1):
        x=iv.sqrt(5+sign*2*u)/3
        weight=(322-sign*13*iv.sqrt(q(70)))/900
        nodes.extend([(-x,weight),(x,weight)])
    h=q(END/N)
    accum=[q(0) for _ in range(3+3*len(PAIRS))]
    for j in range(N):
        cell=8*j//N  # window labels in units 1/32
        for x,b in nodes:
            eta=h*(j+(1+x)/2)
            for i,v in enumerate(readings(eta,cell)):
                accum[i]+=b*v
    # Each analytic piece has |integrand| <= 10^11 on disks of radius 1/128.
    ratio=h*64
    error=2*q(END)*10**11*ratio**10/(1-ratio)
    return [h*v/2+iv.mpf([-1,1])*error for v in accum]


def endpoints(interval):
    vals=[(-1)**s*m*F(2)**e*10**9 for s,m,e,_ in interval._mpi_]
    return [str(F(vals[0]//1,10**9)),str(F(-(-vals[1]//1),10**9))]


def volume_record_and_controls(n=256):
    h=q(END/n)
    tau=norm=filtered=rot=axis=full=mixed=q(0)
    previous=q(0)
    for j in range(n):
        lo,hi=j*h,(j+1)*h
        box=iv.mpf([lo.a,hi.b])
        w,_,k=clock_weight(box)
        duration=h*scale(box)
        t=iv.mpf([tau.a,(tau+duration).b])
        tau+=duration
        norm+=h*abs(k)
        # Same proper-clock weight for both Minkowski and exact vacuum plane-wave controls.
        sech2=4/(iv.exp(t)+iv.exp(-t))**2
        rot-=duration*w*2*(1-t**2)/(1+t**2)**2
        axis-=duration*w*3*sech2
        full+=duration*w*(1/iv.cos(t)**2-sech2)
        mixed-=duration*w*6*(1-3*t**2)/(1+3*t**2)**2
        y_mid=3*iv.ln(iv.cos(lo+hi))/2
        read=q(F(round(float(y_mid.mid)*10**5),10**5))
        assert abs(read-y_mid)<q(".00001")
        right=clock_weight(hi)[1]
        filtered-=read*(right-previous)
        previous=right
    # For other experimental candidates these rate and transfer bounds require independent support.
    assert 3*iv.tan(2*q(END))/scale(q(END))<q("1.1") and tau<q(".44")
    error=norm*(q(".0001")+q("1.1")*iv.sqrt(q(3))*h/2)
    assert 0 in previous and rot<0 and axis<0 and full>0 and mixed<0
    return norm,filtered,error,rot,axis,full,mixed


def calculate():
    H,R,E,*rows=certified_integrals()
    assert 0 in H-R-E and E>0
    norm,read,error,rot,one,three,mixed=volume_record_and_controls()
    assert abs(read-H)<error
    records=[]
    for pair,(delta,parts,C) in zip(PAIRS,zip(rows[::3],rows[1::3],rows[2::3])):
        assert 0 in delta-parts and delta>q(".01") and C>0
        rhs=2*delta**2/C
        guarded=2*(abs(delta)-q(".002"))**2/C
        assert H>R and R>rhs and read-error>guarded and error<guarded
        records.append({"edges_over_32":pair,"signed_contrast_plus":endpoints(delta),
                        "C":endpoints(C),"lower_bound":endpoints(rhs),
                        "lower_after_two_gate_errors":endpoints(guarded)})
    archive=json.loads((BASE/"finite_window_result.json").read_text(),parse_float=F)
    early,late=archive["positive_source_normalized_gate_means"]
    lo,hi=map(F,records[0]["signed_contrast_plus"])
    assert late[0]-early[1]<=lo<=hi<=late[1]-early[0]
    return {"baseline":"7437bd1dec7e84d229c015009b07d698d9739af8",
            "vol_weak_H":endpoints(H),"weighted_Ric":endpoints(R),"weighted_theta2_over3":endpoints(E),
            "gate_checks":records,"volume_bins":256,"sum_from_rounded_log_volumes":endpoints(read),
            "abs_error_for_all_bins":endpoints(error),"integral_abs_w_second":endpoints(norm),
            "rotating_flat_H":endpoints(rot),"one_arm_as_volume_vacuum_H":endpoints(one),
            "three_arms_vacuum_H":endpoints(three),"log_of_summed_volumes_H":endpoints(mixed)}


if __name__=="__main__":
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check",action="store_true")
    args=parser.parse_args()
    result=json.dumps(calculate(),indent=2)
    if args.check:
        assert json.loads(result)==json.loads(Path(__file__).with_name("result.json").read_text())
        print("PASS: weak volume identity, two proper-clock contrasts, binned readout and three vacuum controls")
    else:
        print(result)
