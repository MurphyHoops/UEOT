"""Three compact KG pulses. Recompute all branches and energy intervals."""
import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import sys

from mpmath import iv

HERE = Path(__file__).resolve().parent
QM = HERE.parents[1]
sys.path.insert(0, str(QM / "correlated_bath/field"))
import probe

iv.dps = 48
I = iv.mpc(0, 1)
M = 240
CASES = {"chapter71_local": ("2/3", "3/4", "0", False),
         "chapter71_antipodal": ("1/5", "1/5", "0", True),
         "strict_timelike": ("1/5", "1/5", "5/2", False),
         "strict_spacelike": ("1/5", "1/5", "1/10", True)}


def rat(v):
    f = Fraction(v)
    return iv.mpf(f.numerator)/f.denominator


def decimal(integer, places=13):
    sign = "-" if integer < 0 else ""
    q, r = divmod(abs(integer), 10**places)
    return f"{sign}{q}.{r:0{places}d}"


def bounds(v):
    vals = [(-1)**s * m * Fraction(2)**e * 10**13 for s,m,e,_ in v._mpi_]
    return [decimal(vals[0]//1), decimal(-(-vals[1]//1))]


def con(z):
    return iv.mpc(z.real, -z.imag)


def bracket(x):
    return iv.mpf([-1, 1])*x


def cov(x):
    return [(2*x[0]+x[1])/4, (x[0]+2*x[1])/4]


def dot(coeff, values):
    return sum(a*b for a,b in zip(coeff, values))


def bilinear(left, matrix, right):
    return sum(left[i]*dot(right, matrix[i]) for i in range(3))


def prepare(case, point=False):
    a,b,gap = map(rat, case[:3])
    T = a+gap+b+(rat("13/4") if point else 4)
    h = rat("2/5")
    lam, k = rat("3/10"),rat("-1/10")
    strengths = (lam,lam,k)
    gram = [[iv.mpc(0) for _ in range(3)] for _ in range(3)]
    energy = [[iv.mpc(0) for _ in range(3)] for _ in range(3)]
    lows = []
    on = off = norm = rat(0)
    for j in range(M+1):
        w,g = probe.mode(j)
        parity = (-1)**(j*case[3])
        gb = parity*g
        gc = (rat(1) if j==0 else iv.sqrt(2/w)) if point else gb
        d = [v*f/w*iv.exp(I*w*t)*(1-iv.exp(I*w*dt))
             for v,f,t,dt in zip(strengths,(g,gb,gc),(0,a+gap,T),(a,b,h))]
        if j<2:
            lows.append((w,d))
        norm += gc**2/w if point else w*g**2
        on += 2*k*gc*(iv.exp(-I*w*T)*d[0]).real
        off += -2*k*gc*(iv.exp(-I*w*(T+h))*d[0]).real
        for i in range(3):
            for l in range(i,3):
                z = con(d[i])*d[l]
                gram[i][l] += z
                energy[i][l] += w*z
    # Sum_{j>M} g_j^2 / w_j^r for r=2,1,-1. All kernels use the same f_j.
    pref = 2*(80/iv.pi)**8
    H = pref/(10*probe.beta**3*M**10)
    E = pref/(9*probe.beta**2*M**9)
    HC,EC = (1/(probe.beta**3*M**2), 2/(probe.beta**2*M)) if point else (H,E)
    norm += iv.mpf([0,1])*(EC if point else pref/(7*M**7))
    for i in range(3):
        for l in range(i,3):
            factor = 4*abs(strengths[i]*strengths[l])
            for mat,smooth,c_tail in ((gram,H,HC),(energy,E,EC)):
                tail = smooth if l<2 else (c_tail if i==2 else iv.sqrt(smooth*c_tail))
                if i==l:
                    mat[i][l] = iv.mpc(mat[i][l].real+iv.mpf([0,1])*factor*tail)
                else:
                    err = bracket(factor*tail)
                    mat[i][l] += iv.mpc(err,err)
                    mat[l][i] = con(mat[i][l])
    edge_tail = bracket(4*abs(k*lam)*iv.sqrt(E*EC))
    return gram,energy,lows,on+edge_tail,off+edge_tail,norm


def cases_for_sign(prepared,s):
    G,K,low,on,off,norm = prepared
    zc = rat("3/5")
    x,y = rat("16/25"),rat("-12/25")
    rho_c = [[(1+zc)/2,(x-I*y)/2],[(x+I*y)/2,(1-zc)/2]]
    signs = (1,-1)
    histories = [(s,u,v) for u in signs for v in signs]
    # Ordered Weyl products and normal-ordered field-energy insertion.
    density = {}
    energy_blocks = {}
    e_init = rat("5/4")
    for k,h in enumerate(histories):
        for l,r in enumerate(histories):
            delta = [m-n for m,n in zip(h,r)]
            d_low = [dot(delta,d) for _,d in low]
            nd = cov(d_low)
            angle = sum((h[i]*h[j]-r[i]*r[j]+r[i]*h[j]-r[j]*h[i])*G[i][j].imag
                        for i in range(3) for j in range(i+1,3))
            attenuation = bilinear(delta,G,delta).real/2+sum((con(d)*n).real for d,n in zip(d_low,nd))
            block = rho_c[k%2][l%2]*iv.exp(-attenuation+I*angle)/2
            density[k,l] = block
            insert = e_init+bilinear(r,K,h)
            for (w,d),n in zip(low,nd):
                insert += w*(con(dot(r,d))*n-con(n)*dot(h,d)-con(n)*n)
            energy_blocks[k,l] = block*insert

    def project(mat,b_sign,c_bit):
        # Y_B=b_sign; X_C=+1 for ground, -1 for excitation.
        x_sign = 1-2*c_bit
        ybra = (1,-I*b_sign)
        xbra = (1,x_sign)
        weights = [yb*xb for yb in ybra for xb in xbra]
        v = sum(mat[k,l]*weights[k]*con(weights[l]) for k in range(4) for l in range(4))/4
        assert 0 in v.imag
        return v.real

    joint = {(b,e):project(density,b,e) for b in signs for e in (0,1)}
    e_branch = {key:project(energy_blocks,*key) for key in joint}
    assert all(v>0 for v in joint.values()) and 1 in sum(joint.values())
    p = sum(joint[b,1] for b in signs)
    p_b = joint[1,0]+joint[1,1]
    gain = K[2][2].real+2*s*zc*K[0][2].real
    p_in = (1-x)/2
    dp = p-p_in
    source = K[0][0].real+K[1][1].real
    before = e_init+source
    assert 0 in sum(e_branch.values())-before-gain
    def noise(i):
        v = [d[i] for _,d in low]
        return 2*G[i][i].real+4*sum((con(a)*b).real for a,b in zip(v,cov(v)))
    phase_ab,phase_ac,phase_bc = (4*G[i][j].imag for i,j in ((0,1),(0,2),(1,2)))
    original_z = iv.exp(-noise(1)+I*s*phase_ab)
    final_z = (x-I*y)*iv.exp(-noise(2)+I*s*phase_ac)*iv.cos(phase_bc)
    assert 0 in p_b-(1-original_z.imag)/2 and 0 in p-(1-final_z.real)/2
    switch_on = s*zc*on
    switch_off = s*zc*off+K[2][2].real
    assert 0 in gain-switch_on-switch_off
    pump = dp/2
    data = {"p_e_in":bounds(p_in),"E_F_before_C":bounds(before),"source_work":bounds(source),
            "Phi_AB":bounds(s*phase_ab),"Phi_AC":bounds(s*phase_ac),"Phi_BC":bounds(phase_bc),
            "Q_B":bounds(noise(1)),"Q_C":bounds(noise(2)),"p_B_plusY":bounds(p_b),
            "p_C_e":bounds(p),"delta_E_F":bounds(gain),"delta_E_C":bounds(pump),
            "switch_on":bounds(switch_on),"switch_off":bounds(switch_off),"axis_pump":bounds(pump),
            "net_drive_C_stage":bounds(gain+pump),"total_drive_including_source":bounds(source+gain+pump),
            "p_Yplus_e_minus_product":bounds(joint[1,1]-p_b*p),
            "branches":{("Y+" if b==1 else "Y-")+(",e" if e else ",g"):
                        {"p":bounds(v),"conditional_E_F":bounds(e_branch[b,e]/v)}
                        for (b,e),v in joint.items()}}
    return data,(gain,dp,before,norm,switch_on,joint)


def fixed_axis(raw, gap_text="1/64", point=False):
    # Compare constant lab Z and constant gap with a reference H_C=0.
    gain,dp,before,norm,switch_on,joint = raw
    h,k,gap = rat("2/5"),rat("1/10"),rat(gap_text)
    probability_error = gap*h/2
    field_norm_error = (2*k*gap*h if point else k*gap*h**2/2)*iv.sqrt(norm)
    energy_error = 2*iv.sqrt(before+gain)*field_norm_error+field_norm_error**2
    field = gain+bracket(energy_error)
    excited = dp+bracket(probability_error)
    net = field+gap*excited
    return {"gap":gap_text,"delta_E_F":bounds(field),"delta_p_e":bounds(excited),
            "delta_E_C":bounds(gap*excited),"net_switch_work":bounds(net),
            "switch_on":bounds(switch_on),"switch_off":bounds(net-switch_on),
            "reference_zero_gap_delta_E_F":bounds(gain),"reference_zero_gap_delta_p_e":bounds(dp),
            "all_event_abs_error":bounds(probability_error),"field_energy_abs_error":bounds(energy_error),
            "joint_probability":{("Y+" if b==1 else "Y-")+(",e" if e else ",g"):
                                 bounds(p+bracket(probability_error)) for (b,e),p in joint.items()}}


def calculate():
    data = {"baseline":"940541cd464d8bccb9f7c553dbd3ebfefde596b7","shell_cutoff":M,
            "profile_source_sha256":hashlib.sha256(Path(probe.__file__).read_bytes()).hexdigest(),
            "endpoints":"closed decimal intervals, outward grid 1e-13","cases":{}}
    frozen = json.loads((QM/"cross_domain/heat/result.json").read_text())["cases"]
    for name,case in CASES.items():
        params = prepare(case)
        row = {}
        for s in (1,-1):
            out,raw = cases_for_sign(params,s)
            peer = frozen[name]["signs"][str(s)]
            for key,val in (("Phi_AB",peer["Phi"]),("Q_B",peer["Q"]),("p_B_plusY",peer["Y"]["p_plus"])):
                lo,hi = map(Fraction,out[key])
                a,b = map(Fraction,val)
                assert max(lo,a)<=min(hi,b)
            if name=="chapter71_local" and s==1:
                assert raw[0]<0 and raw[1]>0 and raw[0]+raw[1]/2<0
                assert Fraction(out["p_Yplus_e_minus_product"][0])*Fraction(out["p_Yplus_e_minus_product"][1])>0
            if name=="chapter71_local":
                out["fixed_lab_axis"] = fixed_axis(raw)
            row["+" if s==1 else "-"] = out
        data["cases"][name] = row
    _,point = cases_for_sign(prepare(CASES["chapter71_local"],point=True),1)
    data["point_worldline_fixed_axis"] = fixed_axis(point,"1/128",point=True)
    old = data["cases"]["chapter71_local"]
    for gate in (old["+"]["fixed_lab_axis"],data["point_worldline_fixed_axis"]):
        assert Fraction(gate["delta_E_F"][1])<0 and Fraction(gate["delta_E_C"][0])>0
        assert Fraction(gate["net_switch_work"][1])<0
    assert Fraction(old["+"]["fixed_lab_axis"]["delta_p_e"][0])>Fraction(old["-"]["fixed_lab_axis"]["delta_p_e"][1])
    return data


if __name__=="__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check",action="store_true",help="check all enclosures against the saved result")
    args = parser.parse_args()
    result = calculate()
    if args.check:
        assert result==json.loads((HERE/"result.json").read_text())
        print("PASS: 4 compact source settings x 2 signs x 4 branches, field-energy insertions, 24 source interval checks, fixed-axis extraction")
    else:
        print(json.dumps(result,indent=2))
