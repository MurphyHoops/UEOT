"""Local Hadamard reference on the closed FLRW patch and its two Ramsey qubits."""
from itertools import product

import numpy as np
from scipy.integrate import solve_ivp
from scipy.special import expit, roots_legendre


WINDOWS = ((1/32, 1/16), (5/32, 3/16))
GAIN = 1/20
SIGNS = np.array(list(product((1, -1), repeat=2)))


def rule(lo, hi, order):
    x, w = roots_legendre(order)
    return (hi+lo+(hi-lo)*x)/2, (hi-lo)*w/2


def bump(x):
    return np.exp(-1/(1-x*x))  # called strictly inside (-1,1)


def gates(order, smooth=True):
    x, w = rule(-1, 1, order)
    w *= bump(x) if smooth else (1-x*x)**2
    return np.array([(a+b+(b-a)*x)/2 for a,b in WINDOWS]), w/w.sum()


def field(t):
    return np.sqrt(3)/2*np.arctanh(np.sin(2*t))


def scale_squared(t):
    # Smooth static past on an auxiliary S^3. On the whole readout patch a^2=3 cos(2 eta).
    x = 16*(t+1/8)
    step = 0 if x<=0 else 1 if x>=1 else expit(1/(1-x)-1/x)
    static = np.sqrt(3)
    scale = static+(np.sqrt(3*np.cos(2*t))-static)*step
    return scale**2


def covariance(cutoff, order):
    t, weights = gates(order)
    chi, w = rule(0, .1, order)
    radial = w*np.sin(chi)**2*bump(10*chi)
    n = np.arange(cutoff+1)
    zonal = np.sin((n[:,None]+1)*chi)/(np.sqrt(2)*np.pi*np.sin(chi))
    overlaps = zonal@(radial/radial.sum())
    k2 = n*(n+2)
    k = np.sqrt(k2)
    k[0] = 1.  # massless homogeneous mode: choose its Gaussian width on the initial slice
    mode = 1/np.sqrt(6*k)
    momentum = -1j*np.sqrt(1.5*k)
    def rhs(eta, state):
        u, pi = state.reshape(2,-1)
        a2 = scale_squared(eta)
        return np.r_[pi/a2, -a2*k2*u]
    sol = solve_ivp(rhs, (-1/8, WINDOWS[-1][1]), np.r_[mode, momentum],
                    t_eval=t.ravel(), method="DOP853", rtol=8e-11, atol=1e-12)
    assert sol.success
    u, pi = sol.y.reshape(2,len(n),-1)
    np.testing.assert_allclose((u*pi.conj()-pi*u.conj())[:,-1],1j,rtol=0,atol=2e-7)
    coeff = (u.reshape(len(n),2,order)@weights)*overlaps[:,None]
    two_point = coeff.T@coeff.conj()
    assert np.linalg.eigvalsh(two_point).min()>0
    return two_point


def qubits(mean, two_point, gain):
    # Ordered product U_t^dagger U_s. The same commutator covers all preparations.
    rho = np.empty((4,4),complex)
    comm = 2*two_point.imag
    for i,s in enumerate(SIGNS):
        for j,t in enumerate(SIGNS):
            args = gain*np.array([[t[0],0],[0,t[1]],[0,-s[1]],[-s[0],0]])
            k = args.sum(axis=0)
            phase = k@mean - np.triu(args@comm@args.T,1).sum()/2
            rho[i,j] = np.exp(1j*phase-k@two_point.real@k/2)/4
    np.testing.assert_allclose(rho,rho.conj().T,atol=2e-14)
    assert np.linalg.eigvalsh(rho).min()>-1e-13 and abs(rho.trace()-1)<1e-13
    return rho


def probabilities(rho):
    axes = {"X":np.array([[0,1],[1,0]]),"Y":np.array([[0,-1j],[1j,0]])}
    tables = {}
    for a,b in product(axes,repeat=2):
        p = [np.trace(rho@np.kron((np.eye(2)+i*axes[a])/2,(np.eye(2)+j*axes[b])/2)).real
             for i,j in SIGNS]
        assert min(p)>=-1e-13 and abs(sum(p)-1)<1e-13
        tables[a+b] = list(p)
    return tables
