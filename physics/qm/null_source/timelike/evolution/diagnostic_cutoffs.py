"""Floating-cutoff diagnostics only; these numbers are not RSET certificates.

The original Hamilton mode equation provides a useful scale estimate before
choosing costly validated cutoffs. Neither solver tolerance nor convergence
of this table is an upper bound for the infinite ultraviolet remainder.
"""
import argparse
import hashlib
import importlib.util
import json
import math
from pathlib import Path
import sys
import time
import numpy as np
from scipy.integrate import solve_ivp

HERE=Path(__file__).resolve().parent
TIMELIKE=HERE.parent
sys.path.insert(0,str(TIMELIKE/'instrument'))
spec=importlib.util.spec_from_file_location('_original_instrument',TIMELIKE/'instrument/instrument.py')
original=importlib.util.module_from_spec(spec)
spec.loader.exec_module(original)
TIMES=(0.,3/64,11/64)


def local_terms(t):
    c=math.cos(2*t);h=-math.tan(2*t);q=1/(c*c)
    q1=4*q*math.tan(2*t)
    q2=16*q*math.tan(2*t)**2+8*q*q
    E1=(h*h-1)/2
    E3=(q*q-2*(h*h-1)*q+2*h*q1)/8
    P1=q/3+h*h/2+1/6
    P3=-q*q/8-q2/12-(3*h*h+1)*q/12+h*q1/4
    L=math.log(3*c/4)+2*np.euler_gamma
    rho=((168+180*L)*c*c-110-135*L)/(8640*math.pi**2*c**6)
    p=((160+300*L)*c*c-240-405*L)/(8640*math.pi**2*c**6)
    return E1,E3,P1,P3,rho,p


def one(last):
    k=np.arange(2,last+1,dtype=float)
    omega=np.sqrt(k*k-1)
    a0=math.sqrt(3)
    y=np.concatenate([1/(a0*np.sqrt(2*omega)),-1j*a0*np.sqrt(omega/2)])
    def rhs(t,y):
        u,p=y.reshape(2,-1)
        a=original.state_scale(t)
        return np.concatenate([p/a**2,-a*a*(k*k-1)*u])
    rows=[]
    start=time.monotonic()
    boundaries=[-1/8,-1/16,*TIMES]
    for lo,hi in zip(boundaries,boundaries[1:]):
        sol=solve_ivp(rhs,(lo,hi),y,method='DOP853',rtol=3e-13,atol=1e-14,
                      max_step=min(.0005,1/last))
        if not sol.success: raise RuntimeError(sol.message)
        y=sol.y[:,-1]
        if hi not in TIMES: continue
        u,p=y.reshape(2,-1)
        a=original.scale(hi)
        kinetic=np.abs(p/a)**2
        potential=(k*k-1)*np.abs(a*u)**2
        E1,E3,P1,P3,ra,pa=local_terms(hi)
        E=kinetic+potential-(k+E1/k+E3/k**3)
        P=kinetic-potential/3-(k/3+P1/k+P3/k**3)
        zero=3/(2*a*a)
        # The k=1 subtraction belongs to the same full discrete sum.
        rsum=np.sum(k*k*E,dtype=np.longdouble)+zero-(1+E1+E3)
        psum=np.sum(k*k*P,dtype=np.longdouble)+zero-(1/3+P1+P3)
        rho=float(rsum)/(4*math.pi**2*a**4)+ra
        pressure=float(psum)/(4*math.pi**2*a**4)+pa
        rows.append({'eta':hi,'rho_partial':rho,'pressure_partial':pressure,
                     'effective_SEC_partial':(rho+3*pressure)/2,
                     'wronskian_max_defect':float(np.max(np.abs(-2*np.imag(u.conj()*p)-1)))})
    return {'last_mode':last,'runtime_seconds':round(time.monotonic()-start,3),'points':rows}


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write',action='store_true')
    parser.add_argument('--last',nargs='+',type=int,default=[64,128,256,512])
    args=parser.parse_args()
    data={'schema':'ueot-dynamic-floating-diagnostic/1',
          'source_sha256':hashlib.sha256((TIMELIKE/'instrument/instrument.py').read_bytes()).hexdigest(),
          'method':'DOP853, original u,p Hamilton equations; double precision',
          'certified_error':False,'infinite_tail_included':False,
          'points_are_window_centers_not_window_averages':True,
          'runs':[]}
    for k in args.last:
        row=one(k);data['runs'].append(row);print(json.dumps(row),flush=True)
    if args.write:
        (HERE/'diagnostic.json').write_text(json.dumps(data,indent=2)+'\n')
