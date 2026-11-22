"""Independent review of field/match.py. Called by verify_heat.py."""
from fractions import Fraction as F
from math import comb, factorial
import hashlib
import json

import numpy as np
from mpmath import iv
from scipy.special import roots_legendre, j0


def real_space(order, a, gap, lam):
    # Strictly timelike, image-free. Distribution of eight boxes and two time windows.
    L = 4*np.pi/np.sqrt(5)
    ell = L/160
    p = 2*(1-.6*np.sqrt(.75)/np.sinc(1/80)**4)
    x, w = roots_legendre(order)
    u = (np.arange(8)[:,None]+(x+1)/2).ravel()
    v = np.minimum(u,8-u)
    density = sum((-1)**k*comb(8,k)*np.maximum(v-k,0)**7 for k in range(5))/factorial(7)
    wu = density*np.tile(w/2,8)
    t = np.r_[a*(x+1)/2,a+a*(x+1)/2]
    wt = np.tile(w*a/2,2)*np.minimum(t,2*a-t)/a**2
    radius = L/6+4*ell
    assert gap>2*radius and gap+2*a<L-2*radius
    assert abs(wu.sum()-1)<2e-14 and abs(wt.sum()-1)<2e-14
    value = 0.
    for h,ph in ((0,1-p),(-1,p/2),(1,p/2)):
        for k,pk in ((0,1-p),(-1,p/2),(1,p/2)):
            dx = (h-k)*L/6+2*ell*(u-4)
            green = j0(np.sqrt((gap+t[:,None])**2-dx[None,:]**2))
            value += ph*pk*(wt@green@wu)
    return float(2*L*lam**2*a*a*value)


def review(path, q, bounds, account_at_origin):
    data = json.loads(path.read_text())
    row = data["results"]["strict_timelike"]
    offset, coupling = F(-3,100), F(7,20)
    design_path = path.with_name("design.json")
    design = json.loads(design_path.read_text())
    assert offset not in map(F,design["scale_matching"]["unfitted_offsets"])
    assert abs(offset)<F(design["scale_matching"]["certified_delay_half_window"])
    assert hashlib.sha256(design_path.read_bytes()).hexdigest()==data["design_sha256"]
    a, gap, lam = q("1/5"), q(F(5,2)+offset), q(coupling)
    n,c = q("1/2"),q("1/4")
    # Center form of the pulses and the cosine-transform normalization, coded anew.
    kappa = iv.sqrt(5)/2
    sinc = lambda x:iv.sin(x)/x
    mix = 2*(1-q("3/5")*iv.sqrt(q("3/4"))/sinc(iv.pi/80)**4)
    phi = Q = q(0)
    for j in range(641):
        w = iv.sqrt(1+(j*kappa)**2)
        g = q(1) if j==0 else iv.sqrt(2/w)*sinc(j*iv.pi/80)**4*(1-mix+mix*iv.cos(j*iv.pi/3))
        u = g*a*sinc(w*a/2)
        phi += 4*lam**2*u**2*iv.sin(w*(gap+a))
        Q += 2*lam**2*u**2
        if j==0:
            w0,u0 = w,u
        if j==1:
            assert q("3/5") in g
            Q += 4*lam**2*(n*(u0**2+u**2)+2*c*u0*u*iv.cos((w-w0)*(gap+3*a/2)))
            low_phi, low_Q = phi,Q
    H = 2*(80/iv.pi)**8/(10*kappa**3*640**10)
    phi += iv.mpf([-16,16])*lam**2*H
    Q += iv.mpf([0,8])*lam**2*H

    def box(pair):
        return iv.mpf([q(F(pair[0])).a,q(F(pair[1])).b])
    pe = low_phi+lam**2*sum(box(v)*q(offset)**j for j,v in enumerate(row["coefficients_unit_lambda"]))
    ne = low_Q+lam**2*box(row["matched_high_Q_unit_lambda"])
    def prob(p,e):
        return (1-iv.exp(-e)*iv.sin(p))/2
    ep,eq,eb = abs(phi-pe),abs(Q-ne),abs(prob(phi,Q)-prob(pe,ne))
    qbound = 8*q("2/5")**2*2*(80/iv.pi)**8/(10*kappa**3*160**10)
    assert ep<box(row["uniform_phase_error_rad"]) and eb<box(row["uniform_binary_error"]) and eq<qbound
    position = [real_space(k,.2,float(F(5,2)+offset),float(coupling)) for k in (8,16)]
    assert max(abs(v-float(phi.mid)) for v in position)<2e-13
    # A JC pulse that swaps |e,0> fails on |e,1>, which the required SWAP fixes.
    jc_error = iv.sin(iv.pi*iv.sqrt(2)/2)**2
    assert jc_error>q(".6")
    # Z_B times any smeared field commutes with the B energy projector.
    required_population_change = box(account_at_origin["original_field_gain_first_swap"])
    assert required_population_change > q(".15")
    return {"peer_design_sha256":data["design_sha256"],"peer_result_sha256":hashlib.sha256(path.read_bytes()).hexdigest(),
            "peer_match_sha256":hashlib.sha256(path.with_name("match.py").read_bytes()).hexdigest(),
            "strict_timelike_offset":str(offset),"lambda":str(coupling),"last_shell":640,
            "direct_phi_Q_pY":[bounds(x) for x in (phi,Q,prob(phi,Q))],
            "matched_phi_Q_pY":[bounds(x) for x in (pe,ne,prob(pe,ne))],
            "errors_phi_Q_pY":[bounds(x) for x in (ep,eq,eb)],
            "allowed_phi_Q_pY":[row["uniform_phase_error_rad"],bounds(qbound),row["uniform_binary_error"]],
            "real_space_J0_quadrature_orders_8_16":position,"abs_error_wrong_JC_transfer_on_e1":bounds(jc_error),
            "original_QND_B_population_error_if_used_as_SWAP":account_at_origin["original_field_gain_first_swap"]}
