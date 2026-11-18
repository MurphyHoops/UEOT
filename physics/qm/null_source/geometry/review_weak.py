"""Independent sign and shear checks for the parent weak-lens contract."""
from fractions import Fraction as F
import hashlib
import json
from pathlib import Path
import sys

import numpy as np
from scipy.integrate import solve_ivp
from scipy.special import roots_legendre

ROOT=Path(__file__).resolve().parent.parent
sys.path.insert(0,str(ROOT))
import weak_lens as parent


def source(u):
    t=1-u*u
    f=np.exp(1-1/t)
    fp=-2*u*f/t**2
    fpp=f*(4*u*u/t**4-8*u*u/t**3-2/t**2)
    return f*f,fp*fp,2*(fp*fp+f*fpp)


def trajectories(h,xi,hidden=False):
    def rhs(u,state):
        F0,X,Fpp=source(u)
        K=h*(X-xi*Fpp)/(1-2*h*xi*F0)
        W=np.array([[(1+u)/8,u/10],[u/10,-(1+u)/8]])
        M=np.diag([0.,2*K]) if hidden else np.eye(2)*K+W
        J,V=state.reshape(2,2,2)
        return np.stack([V,-M@J]).ravel()
    sol=solve_ivp(rhs,(-.75,.75),np.stack([np.eye(2),np.zeros((2,2))]).ravel(),
                  method="DOP853",max_step=.025,rtol=1e-12,atol=2e-15,dense_output=True)
    assert sol.success
    return lambda u:sol.sol(u).T.reshape(-1,2,2,2)


def test_rows(n,trace):
    # Direct unintegrated identity uses Kz. Parent kernels transfer derivatives to w,wF.
    nodes,weights=roots_legendre(n)
    u=.75*nodes
    J,V=trace(u).transpose(1,0,2,3)
    z,d=np.linalg.det(J),np.linalg.det(V)
    f2,X,Fpp=source(u)
    h,b=1/16,1/96
    K=(h*X-b*Fpp)/(1-2*b*f2)
    cell = np.array([[[float(s[0].mid) for s in row]
                      for row in parent.kernels(parent.rational(F(str(t))),0)] for t in u])
    out=[]
    for idx,power in enumerate((0,2)):
        ker=cell[:,idx,:].T
        w=(1-(4*u/3)**2)**3*u**power
        direct = np.array([w*K*z,w*z*X,w*z*(2*f2*K-Fpp)])
        weak=np.array([ker[0]*z+ker[1]*d,ker[2]*z,ker[3]*z+ker[4]*d])
        weights_u=.75*weights
        L,M,B=weak@weights_u
        wrong=B+(2*w*Fpp*z)@weights_u  # flip -wF'' to +wF'' only
        diff=np.max(abs((weak-direct)@weights_u))
        assert diff<3e-13 and abs(L-h*M-b*B)<1e-13
        assert abs(L-h*M-b*wrong)>3e-4
        out.append({"L_M_B":[float(x) for x in (L,M,B)],"sign_flipped_residual":float(L-h*M-b*wrong),
                    "max_direct_vs_by_parts":float(diff)})
    return out


def review():
    # Exact coefficients in the order L_z,L_d,M_z,B_z,B_d at the center.
    expected=((F(16,3),1,0,F(56,3),2),(-1,0,0,-2,0))
    for row,ref in zip(parent.kernels(parent.rational(0),0),expected):
        assert all(parent.rational(x).a>=s[0].a and parent.rational(x).b<=s[0].b
                   for s,x in zip(row,ref))
    a=test_rows(64,trajectories(1/16,1/6))
    b=test_rows(96,trajectories(1/16,1/6))
    assert all(abs(x["sign_flipped_residual"]-y["sign_flipped_residual"])<1e-13 for x,y in zip(a,b))
    grid=np.linspace(-.75,.75,129)
    rails=[trajectories(h,xi,hidden=True)(grid) for h,xi in ((1/16,1/6),(9/64,0))]
    for run in rails:
        assert np.all(run[:,0,0,0]==1) and np.all(run[:,1,0,0]==0)
    y=[float(run[-1,0,1,1]) for run in rails]
    assert abs(y[0]-y[1])>.01
    return {"parent_weak_lens_sha256":hashlib.sha256((ROOT/"weak_lens.py").read_bytes()).hexdigest(),
            "rows_96":b,"hidden_rail_x_in_both":[1,0],"other_rail_exit_positions":y}


if __name__=="__main__":
    print(json.dumps(review(),indent=2))
