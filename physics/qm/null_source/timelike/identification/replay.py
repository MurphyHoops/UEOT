"""Recompute the timelike blind preparations and audit the finite-frequency variance claim."""
import argparse
import json
from pathlib import Path
import sys

import numpy as np
import sympy as sp
from mpmath import mp
from scipy.special import expit

from reference import GAIN, WINDOWS, bump, covariance, field, gates, probabilities, qubits, rule, scale_squared


def preparation_energy(p, q, sigma, order):
    # Initial proper energy difference integrated through an explicit smooth cutoff.
    a = np.sqrt(3)
    inside,w = rule(0,1/2,order)
    edge,v = rule(1/2,9/16,order)
    t = 16*(edge-.5)
    growth = 1/(1-t)-1/t
    taper = np.r_[np.ones(order),expit(-growth)]
    derivative = np.r_[np.zeros(order),-16*expit(growth)*expit(-growth)*(1/t**2+1/(1-t)**2)]
    x = np.r_[inside,edge]
    f = 1.5*(x-np.sin(x)*np.cos(x))/np.sin(x)**2
    df = 3-2*f/np.tan(x)
    volume = 4*np.pi*a**3*np.r_[w,v]*np.sin(x)**2
    dipole = sigma**2/(2*a*a)*((taper*df+derivative*f)**2+2*(taper*f/np.sin(x))**2)
    alias = ((p*taper)**2+(q*derivative/a)**2)/2
    return np.array([volume@dipole,volume@alias])


def spatial_kernel():
    chi = sp.symbols("chi", positive=True)
    f = 3*(chi-sp.sin(chi)*sp.cos(chi))/(2*sp.sin(chi)**2)
    assert sp.trigsimp(f.diff(chi)+2*sp.cot(chi)*f-3)==0
    assert sp.trigsimp(f.diff(chi,2)+2*sp.cot(chi)*f.diff(chi)-2*f/sp.sin(chi)**2)==0
    assert sp.limit(f/chi,chi,0)==1
    sigma = .25  # standard deviation of each of three independent Gaussian displacements
    densities = [3*sigma**2/(2*3*np.cos(2*t)) for t in (0,.125,.25)]
    x,w = rule(1/8,3/16,80)
    shell = w*np.sin(x)**2*bump((x-5/32)/(1/32))
    mean_f = np.average(sp.lambdify(chi,f,"numpy")(x),weights=shell)
    z,w = rule(-1,1,80)  # z = cos(theta)
    odd_mean = mean_f*(w@(z*(1+z)))/2
    assert abs(w@z)<2e-16 and abs(odd_mean-mean_f/3)<1e-14
    ratio = np.exp(-.5*(2*GAIN*sigma*odd_mean)**2)
    assert .99<ratio<1 and 3/16+1/4<.5<9/16<np.arcsin(1/np.sqrt(3))
    return dict(center_extra_density=densities, center_extra_pressure=[-v/3 for v in densities],
                directional_mean_mode=odd_mean, directional_visibility_ratio=ratio)


def bacon_comparison(tables, cov, mu):
    # Read the independently evolved amplitudes and retarded response only after our integration.
    directory=Path(__file__).resolve().parents[1]/"instrument"
    peer=json.loads((directory/"result.json").read_text())
    sys.path.insert(0,str(directory))
    try:
        from instrument import output_table, state_scale
    finally:
        sys.path.pop(0)
    assert peer["g"]==GAIN
    smooth=peer["smooth"]
    for t in np.linspace(-1/8,0,129):
        assert abs(scale_squared(t)-state_scale(t)**2)<3e-15
    np.testing.assert_allclose(mu,smooth["means"],rtol=0,atol=2e-14)
    weighted_cov_error=float(abs(GAIN**2*cov.real-smooth["covariance"]).max())
    retarded=2*GAIN**2*cov[0,1].imag
    comm_error=abs(retarded-smooth["retarded_pair"])
    assert weighted_cov_error<2e-13 and comm_error<1e-13
    errors={}
    for sign in (1,-1):
        errors[str(sign)]={}
        for axes,values in tables[str(sign)].items():
            key=axes+("_plus" if sign==1 else "_minus")
            peer_table=output_table(smooth,sign=sign,axes=axes)
            if key in smooth:
                np.testing.assert_allclose(peer_table,smooth[key],rtol=0,atol=2e-15)
            gap=float(abs(np.reshape(values,(2,2))-peer_table).max())
            assert gap<5e-13,(sign,axes,gap)
            errors[str(sign)][axes]=gap
    return dict(max_cell_error_by_sign_axes=errors, weighted_covariance_max_error=weighted_cov_error,
                weighted_commutator=retarded,peer_retarded_pair=smooth["retarded_pair"],
                weighted_commutator_error=comm_error)


def mean_and_tables():
    t,w = gates(128)
    mu = field(t)@w
    old_t,old_w = gates(128,smooth=False)
    old_mu = field(old_t)@old_w
    old = json.loads((Path(__file__).resolve().parents[2]/"finite_window_result.json").read_text())
    assert all(lo<x<hi for x,(lo,hi) in zip(old_mu,old["positive_source_normalized_gate_means"]))
    rough = covariance(300,128)
    cov = covariance(800,192)
    err = float(abs(rough-cov).max())
    assert err<2e-8
    turn = 2*np.pi/(2*GAIN)
    p = turn/(mu[1]-mu[0])
    q = -p*mu[0]
    h = q+p*mu
    np.testing.assert_allclose(h,[0,turn],atol=1e-12,rtol=0)
    tables = {}
    original_error = 0.
    for sign in (-1,1):
        base = qubits(sign*mu,cov,GAIN)
        other = (qubits(sign*mu+h,cov,GAIN)+qubits(sign*mu-h,cov,GAIN))/2
        original_error = max(original_error,float(abs(other-base).max()))
        np.testing.assert_allclose(other,base,atol=2e-14,rtol=0)
        tables[str(sign)] = probabilities(base)
    v = np.exp(-.5*(2*GAIN)**2*cov.diagonal().real)
    single = v*np.exp(2j*GAIN*mu)
    half = np.exp(-.5*GAIN**2*cov[1,1].real+1j*GAIN*mu[1])
    half_other = half*np.cos(GAIN*h[1])
    assert abs(half_other+half)<1e-14
    energy=preparation_energy(p,q,.25,128)
    np.testing.assert_allclose(energy,preparation_energy(p,q,.25,80),rtol=2e-10,atol=1e-12)
    return dict(smooth_gate_means=mu.tolist(), legacy_means=old_mu.tolist(),
                initial_proper_extra_energy=dict(dipoles=energy[0],homogeneous_alias=energy[1]),
                reference_W_real=cov.real.tolist(),reference_W_imag=cov.imag.tolist(),
                cutoff_300_800_max_change=err, bacon_comparison=bacon_comparison(tables,cov,mu),
                single_visibility=v.tolist(),
                single_positive_source_Xplus=((1+single.real)/2).tolist(),
                single_positive_source_Yplus=((1+single.imag)/2).tolist(),
                joint_XY_tables=tables, joint_outcome_order=["++","+-","-+","--"],
                homogeneous_alias=dict(initial_offset=q,initial_extra_velocity=p,extra_density_initial=p**2/2,
                    extra_density_final=p**2/(2*np.cos(.5)**3),joint_state_max_error=original_error,
                    half_gain_gate2_Xplus=[(1+half.real)/2,(1+half_other.real)/2]))


def fourth_moment_audit():
    # Independent bound via the induced matrix norm. The reviewer's polynomial gates use 2g=1.
    mp.dps = 85
    def mean(lo,hi):
        def integrand(x):
            t=lo+(hi-lo)*x
            return 30*x*x*(1-x)**2*mp.sqrt(3)/2*mp.atanh(mp.sin(2*t))
        return mp.quad(integrand,[0,1])
    a,b=[mean(mp.mpf(lo),mp.mpf(hi)) for lo,hi in WINDOWS]
    frequencies=[a,b,b-a,a+b]
    js=list(range(6))
    mat=mp.matrix([[1]*6,[j*j for j in js]]+[[mp.cos(6*j*f) for j in js] for f in frequencies])
    norm=mp.mnorm(mat**-1,"inf")
    small=mp.mpf(3)/(4*36*55)
    base=mp.matrix([1-5*small]+[small]*5)
    gamma=small/(4*norm)
    def powered(law,k):
        return sum(w*(6*j)**k for j,w in law.items())
    def tagged(law):
        # E[Y^2 cos(aY)] on the positive preparation, before multiplying by visibility.
        return sum(w*(y+mp.mpf(".5"))**2*mp.cos(a*(y+mp.mpf(".5")))/2
                   for j,w in law.items() for y in (-6*j,6*j))
    baseline=dict(enumerate(base))
    out=[]
    for N in (10000,1000000):
        rhs=mp.matrix([1,N*N]+[mp.cos(6*N*f) for f in frequencies])
        c=mp.lu_solve(mat,rhs)
        tail=gamma/N**2
        law=dict(enumerate(base-tail*c))
        law[N]=tail
        assert min(law.values())>0 and abs(sum(law.values())-1)<mp.mpf("1e-65")
        assert abs(powered(law,2)-mp.mpf(".75"))<mp.mpf("1e-65")
        gaps=[abs(sum(w*mp.cos(6*j*f) for j,w in law.items())
                  -sum(w*mp.cos(6*j*f) for j,w in baseline.items())) for f in frequencies]
        assert max(gaps)<mp.mpf("1e-65")
        gain=powered(law,4)-powered(baseline,4)
        tagged_gap=tagged(law)-tagged(baseline)
        assert gain>gamma*6**4*(N**2-6*norm*5**4) and abs(tagged_gap)>mp.mpf("1e-12")
        out.append(dict(N=N,tail=float(tail),fourth_increase=float(gain),
                        Xplus_cosine_weighted_Y2_change=float(tagged_gap)))
    return dict(matrix_inverse_inf_norm=float(norm),polynomial_frequencies=list(map(float,frequencies)),trials=out)


def compare(a,b):
    if isinstance(a,dict):
        assert a.keys()==b.keys()
        for k in a:
            if k=="joint_state_max_error":
                assert max(a[k],b[k])<2e-14
            elif k=="cutoff_300_800_max_change":
                assert max(a[k],b[k])<2e-8
            elif k in ("weighted_covariance_max_error","weighted_commutator_error"):
                np.testing.assert_allclose(a[k],b[k],rtol=0,atol=5e-15)
            elif k=="max_cell_error_by_sign_axes":
                assert a[k].keys()==b[k].keys()
                for sign in a[k]:
                    assert a[k][sign].keys()==b[k][sign].keys()
                    for axis,value in a[k][sign].items():
                        np.testing.assert_allclose(value,b[k][sign][axis],rtol=0,atol=5e-15)
            else:
                compare(a[k],b[k])
    elif isinstance(a,list):
        assert len(a)==len(b)
        for x,y in zip(a,b):
            compare(x,y)
    elif isinstance(a,(float,int)):
        np.testing.assert_allclose(a,b,rtol=2e-8,atol=1e-18)
    else:
        assert a==b


if __name__=="__main__":
    if not __debug__:
        raise RuntimeError("run with assertions enabled")
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check",action="store_true")
    args=parser.parse_args()
    result=dict(baseline="7437bd1dec7e84d229c015009b07d698d9739af8", spatial=spatial_kernel(),
                instrument=mean_and_tables(), fluctuation=fourth_moment_audit())
    if args.check:
        compare(result,json.loads(Path(__file__).with_name("observed.json").read_text()))
        print("PASS: KG, fixed-background stress, both signs and joint XY menus, new operations, conditioned moment")
    else:
        print(json.dumps(result,indent=2,allow_nan=False))
