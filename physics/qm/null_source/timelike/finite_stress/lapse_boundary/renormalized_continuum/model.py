"""Shared analytical primitives for the renormalized continuum apparatus and closed-FRW bounce."""
from __future__ import annotations
import sympy as sp
from common import iv,require

# Exact rational polynomials alpha_1(c0)..alpha_9(c0) for (cos(chi)-c0)^8 * sin(chi) = sum_{m=1}^9 alpha_m(c0) sin(m*chi)
def _build_alpha_polys():
    z,c0=sp.symbols("z c0")
    poly_z=sp.expand((z**2+1-2*c0*z)**8*(z**2-1))
    out=[]
    for m in range(1,10):
        cm=sp.Poly(sp.simplify(sp.Poly(poly_z,z).nth(9+m)/sp.Integer(256)),c0)
        out.append([((deg,),int(cf.p),int(cf.q)) for (deg,),cf in cm.terms()])
    u_s,s_s,c_s=sp.symbols("u s c")
    P=u_s**8
    derivs=[P]
    for _ in range(9):
        P=sp.expand(-s_s*sp.diff(P,u_s)+c_s*sp.diff(P,s_s)-s_s*sp.diff(P,c_s))
        derivs.append(P)
    sin_d=[s_s,c_s,-s_s,-c_s]*3
    g9=sp.expand(sum(sp.binomial(9,j)*derivs[j]*sin_d[9-j] for j in range(10)))
    g9_terms=[(du,ds,dc,int(cf)) for (du,ds,dc),cf in sp.Poly(g9,u_s,s_s,c_s).terms()]
    return out,g9_terms

ALPHA_POLYS,G9_TERMS=_build_alpha_polys()

def _isin(m,k,r0):
    if k==m:
        return r0/2-iv.sin(2*k*r0)/(4*k)
    return iv.sin((k-m)*r0)/(2*(k-m))-iv.sin((k+m)*r0)/(2*(k+m))

def geodesic_cap_spectrum(inv_r0=20,Kmax=512,nsub=32):
    r0=iv.mpf(1)/inv_r0
    require(r0.a>0 and r0.b<(iv.pi/2).a,"Cap radius must lie in (0, pi/2)")
    c0=iv.cos(r0)
    alphas=[None]
    for terms in ALPHA_POLYS:
        v=iv.mpf(0)
        for (deg,),p_num,q_den in terms:
            v+=(iv.mpf(p_num)/q_den)*(c0**deg)
        alphas.append(v)
    I1=sum(alphas[m]*_isin(m,1,r0) for m in range(1,10))
    C_r0=4*iv.pi*I1
    require(C_r0.a>0,"Positive geodesic-cap normalization")
    khat=[]
    for k in range(1,Kmax+1):
        Ik=sum(alphas[m]*_isin(m,k,r0) for m in range(1,10))
        khat.append(4*iv.pi*Ik/(C_r0*k))
    int_g9=iv.mpf(0)
    for idx in range(nsub):
        a_i=r0*idx/nsub;b_i=r0*(idx+1)/nsub
        s_hi=iv.sin(b_i);c_hi=iv.cos(a_i);u_hi=c_hi-c0
        val=iv.mpf(0)
        for du,ds,dc,cf in G9_TERMS:
            val+=iv.mpf(abs(cf))*(u_hi**du)*(s_hi**ds)*(c_hi**dc)
        int_g9+=val*(r0/nsub)
    B_r0=4*iv.pi*(40320*iv.sin(r0)**9+int_g9)/C_r0
    return {"rho0":r0,"cos_rho0":c0,"C_rho0":C_r0,"B_rho0":B_r0,"khat":khat,"alphas":alphas[1:]}

def power_tail_upper(exponent,Ksplit):
    """Rigorous integral-comparison enclosure for sum_{k=Ksplit+1}^infty k^(-exponent), exponent > 1."""
    require(exponent>1 and Ksplit>=1,"Convergent power tail required")
    p=iv.mpf(exponent)
    return (iv.mpf(Ksplit)**(1-p))/(p-1)

def frw_bounce_enclosure(alpha_G=None,lam_L=None,N=220,T_end=None):
    """Exact Taylor-Picard outward-interval enclosure of u(tau)=a(tau)^2 for
    u'' = 2*(3*lam_L*u^2 - 2*u + beta_r), u(0)=1, u'(0)=0, beta_r = 1 - alpha_G - lam_L,
    with ZERO ODE integrations."""
    if alpha_G is None:alpha_G=iv.mpf(1)/10
    if lam_L is None:lam_L=iv.mpf(550001)/1000000
    if T_end is None:T_end=iv.pi+3
    beta_r=1-alpha_G-lam_L
    eps0=2*lam_L-1-alpha_G
    mu0=3*lam_L-1
    require(alpha_G.a>0 and beta_r.a>0 and eps0.a>0 and mu0.a>0,"Sub-critical bounce regime")
    # Even polynomial coefficients c[0..N] of u_N(tau) = 1 + sum_{n=2}^N c[n] tau^n
    c=[iv.mpf(0)]*(N+1)
    c[0]=iv.mpf(1)
    for n in range(0,N-1):
        u2_n=sum(c[j]*c[n-j] for j in range(n+1))
        rhs_n=2*(3*lam_L*u2_n-2*c[n]+(beta_r if n==0 else 0))
        c[n+2]=rhs_n/((n+1)*(n+2))
    require(all(c[n].a>=0 for n in range(N+1)),"Nonnegative Taylor coefficients required for monotone defect bound")
    # Exact ODE residual d_N(tau) = 6*lam_L*u_N^2 - 4*u_N + 2*beta_r - u_N''
    # = 4*mu0*(w_c[N-1]*tau^(N-1) + w_c[N]*tau^N) + 6*lam_L * sum_{m=N-1}^{2N} (sum_{j+k=m, 2<=j,k<=N} c[j]*c[k]) tau^m
    w_c=[iv.mpf(0) if i==0 else c[i] for i in range(N+1)]
    defect_T=4*mu0*(w_c[N-1]*(T_end**(N-1))+w_c[N]*(T_end**N))
    for m in range(N-1,2*N+1):
        conv=iv.mpf(0)
        j_lo=max(2,m-N);j_hi=min(N,m-2)
        for j in range(j_lo,j_hi+1):
            conv+=w_c[j]*w_c[m-j]
        defect_T+=6*lam_L*conv*(T_end**m)
    w_T=sum(w_c[n]*(T_end**n) for n in range(2,N+1))
    # Write r = u - u_N; r'' = (4*mu0 + 12*lam_L*w_N)*r + 6*lam_L*r^2 + d_N(tau), where 12*lam_L - 4 = 4*mu0.
    # Weighted Banach norm ||r||_gamma = sup_{|tau|<=T_end} exp(-gamma*|tau|)*|r(tau)| with gamma = 3:
    gamma=iv.mpf(3)
    lin_coef_T=4*mu0+12*lam_L*w_T
    L_lin=lin_coef_T/(gamma**2)
    require(L_lin.b<iv.mpf("0.45"),"Weighted linear Picard contraction < 0.45")
    src_sup=(T_end**2/2)*defect_T
    egT=iv.exp(gamma*T_end)
    rho_g=2*src_sup/(1-L_lin)
    quad_term=(6*lam_L*egT/(gamma**2))*(rho_g**2)
    L_lip=L_lin+(12*lam_L*egT/(gamma**2))*rho_g
    require((L_lin*rho_g+quad_term+src_sup).b<rho_g.a and L_lip.b<iv.mpf("0.5"),"Strict Banach self-map and Lipschitz contraction")
    R_u=egT*rho_g
    R_up=T_end*(lin_coef_T*R_u+6*lam_L*(R_u**2)+defect_T)
    R_upp=lin_coef_T*R_u+6*lam_L*(R_u**2)+defect_T
    return {"alpha_G":alpha_G,"lam_L":lam_L,"beta_r":beta_r,"eps0":eps0,"mu0":mu0,
            "N":N,"T_end":T_end,"coeffs":c,"w_T_poly":w_T,"R_u":R_u,"R_up":R_up,"R_upp":R_upp}

def eval_frw(enc,tau_iv):
    require(abs(tau_iv).b<=enc["T_end"].b,"Evaluation time outside certified [-T_end, T_end]")
    c=enc["coeffs"];N=enc["N"]
    u_p=sum(c[n]*(tau_iv**n) for n in range(N+1))
    up_p=sum(n*c[n]*(tau_iv**(n-1)) for n in range(1,N+1))
    upp_p=sum(n*(n-1)*c[n]*(tau_iv**(n-2)) for n in range(2,N+1))
    ru=iv.mpf([-enc["R_u"].b,enc["R_u"].b])
    rup=iv.mpf([-enc["R_up"].b,enc["R_up"].b])
    rupp=iv.mpf([-enc["R_upp"].b,enc["R_upp"].b])
    u=u_p+ru;up=up_p+rup;upp=upp_p+rupp
    require(u.a>0,"Scale factor squared must remain strictly positive")
    a=iv.sqrt(u)
    ap=up/(2*a)
    app=(2*u*upp-up**2)/(4*u*a)
    return {"u":u,"up":up,"upp":upp,"a":a,"ap":ap,"app":app}
