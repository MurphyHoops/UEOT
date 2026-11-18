"""Interval lower bound for the original smooth central aperture, unit phase gains."""
from mpmath import iv


def certificate():
    # All inputs to interval functions are integers or exact dyadics/rationals.
    iv.dps = 32
    one = iv.mpf(1)
    R = one/10
    normal = iv.sqrt(2)*iv.pi
    cells = 512
    x = [(i+one/2)/cells for i in range(cells)]
    bump = [iv.exp(-1/(1-y*y)) for y in x]
    sin_rx = [iv.sin(R*y)/R for y in x]
    def mid(values, derivative_bound):
        error = one*derivative_bound/(24*cells**2)
        return sum(values)/cells + iv.mpf([-1,1])*error
    mass = mid(bump,32)
    radial_mass = mid([b*s*s for b,s in zip(bump,sin_rx)],40)
    def a(t):
        return iv.sqrt(3*iv.cos(2*t))
    def phi(t):
        return iv.sqrt(3)*iv.ln((1+iv.sin(2*t))/iv.cos(2*t))/2
    def step(k):
        if k in (0,8):
            return one*k/8
        z = one*k/8
        return 1/(1+iv.exp(1/z-1/(1-z)))
    past_var = iv.ln(a(0)/a(-one/16))
    for k in range(8):
        lo = -one/8+one*k/128
        hi = lo+one/128
        past_var += ((a(hi)-a(lo))*step(k+1)+(a(0)-a(lo))*(step(k+1)-step(k)))/a(-one/8)
    assert past_var < iv.mpf(".020")
    centers = [3*one/64,11*one/64]
    means = [mid([b*(phi(c+y/64)+phi(c-y/64))/2 for b,y in zip(bump,x)],20)/mass
             for c in centers]
    diagonal = [one*0,one*0]
    cross = one*0
    error_sq = one*0
    for n in range(2,65):
        nu = iv.sqrt(n*n-1)
        radial = mid([b*s*iv.sin(n*R*y) for b,s,y in zip(bump,sin_rx,x)],75)
        f = radial/(R*normal*radial_mass)
        time = mid([b*iv.cos(nu*y/64) for b,y in zip(bump,x)],36)/mass
        moduli = [f*time/(iv.sqrt(2*nu)*a(c)) for c in centers]
        cross += moduli[0]*moduli[1]*iv.cos(nu*(centers[1]-centers[0]))
        for i,c in enumerate(centers):
            diagonal[i] += moduli[i]**2
            hi = c+one/64
            gain_error = (a(0)/a(hi)-1)/a(hi)
            # 1/a increases convexly over both windows.
            gain_error += 1/a(hi)-1/a(c)
            error_sq += f**2*gain_error**2/(2*nu)
    d1,d2 = diagonal
    smallest = (d1+d2-iv.sqrt((d1-d2)**2+4*cross**2))/2
    margin = iv.sqrt(smallest)-iv.sqrt(error_sq)
    assert margin>0
    eigen_bound = iv.exp(-2*past_var)*margin**2
    assert eigen_bound>2, eigen_bound
    s_cap = sum(v**2 for v in means)/2
    assert s_cap < iv.mpf(".04946"), s_cap
    assert (one*3/4)*s_cap**2*iv.exp(-2) < iv.mpf(".00024831")
    assert iv.exp(-2/s_cap) < iv.mpf("2.75e-18")
    return dict(modes=[2,64],midpoint_cells=cells,unit_lambda_min_lower=2,
                prior_log_scale_variation_upper=.020,
                mean_intervals_outward=[[float(v.a)-1e-15,float(v.b)+1e-15] for v in means],
                surrogate_lambda_lower=float(smallest.a)-1e-12,
                amplitude_error_upper=float(iv.sqrt(error_sq).b)+1e-12,
                low_modes_lambda_lower=float(eigen_bound.a)-1e-12,
                s_upper=.04946,all_gain_single_probability_gap_upper=.00024831,
                visibility_upper_at_t2=2.75e-18)
