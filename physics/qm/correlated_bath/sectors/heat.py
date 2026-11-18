"""An energy-exchange endpoint with explicit work, entropy, mixing and memory."""
import json
import math
import numpy as np


def entropy(p):
    return -sum(s*math.log(s) for s in p if s>0)


def main():
    theta=math.pi/6
    q=.2
    initial=.8
    U=np.eye(4,dtype=complex)
    U[1:3,1:3]=[[math.cos(theta),-1j*math.sin(theta)],[-1j*math.sin(theta),math.cos(theta)]]
    H=np.diag([0,1,1,2])
    assert np.linalg.norm(U@H-H@U)<1e-14
    source=np.kron(np.diag([1-initial,initial]),np.diag([1-q,q]))
    y=U@source@U.conj().T
    pS=(y[2,2]+y[3,3]).real
    pE=(y[1,1]+y[3,3]).real
    assert abs(pS-(q+(initial-q)*.75))<1e-13
    assert abs(pS+pE-initial-q)<1e-13
    # Projective energy record of E. All outcomes retained. Reinitialize S to its initial distribution
    # as a distinct controlled preparation in the persistent-vs-refreshed comparison.
    conditional=[float(y[2+b,2+b].real/(y[b,b]+y[2+b,2+b]).real) for b in (0,1)]
    beta=math.log((1-q)/q)
    sigma=entropy([pS,1-pS])-entropy([initial,1-initial])+beta*(pE-q)
    assert sigma>=0 and abs(sum(p*pr for p,pr in zip(conditional,[1-pE,pE]))-pS)<1e-13
    assert abs((initial*.75+pE*.25)-(initial*.75+q*.25))>0.03
    print(json.dumps(dict(first_system_excited=pS,first_bath_excited=pE,
       source_switch_work_ideal=0,system_energy_gain=pS-initial,bath_energy_gain=pE-q,
       entropy_production=sigma,terminal_system_excited_given_bath_0_1=conditional,
       fresh_population_contraction=.75,persistent_minus_fresh_next_after_reprepare=.25*(pE-q),
       record_erase_work_lower_unassisted_at_beta=entropy([pE,1-pE])/beta),indent=2))


if __name__=="__main__":
    main()
