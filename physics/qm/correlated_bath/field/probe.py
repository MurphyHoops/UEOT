"""Interval enclosure for the causal-break probe on the massive KG cylinder."""
import json
from mpmath import iv

iv.dps = 45
R = iv.mpf
beta = iv.sqrt(5) / 2
length = 2 * iv.pi / beta
scale = R(3) / 10
occupation = R(1) / 2
correlation = R(1) / 4


def mode(j):
    if j == 0:
        return R(1), R(1)
    x = iv.pi * j / 80
    x1 = iv.pi / 80
    target = R(3) / 5 * iv.sqrt(R(3) / 4)
    mix = 2 * (1 - target / (iv.sin(x1) / x1)**4)
    assert 0 < mix and mix < 1
    profile = (iv.sin(x) / x)**4 * (1 - mix + mix * iv.cos(iv.pi * j / 3))
    w = iv.sqrt(1 + (beta * j)**2)
    return w, iv.sqrt(2 / w) * profile


def display(x):
    # Preserve decimal endpoints as exact dyadic encodings in the receipt.
    return {"dyadic": [list(v) for v in x._mpi_], "mid_approx": float(x.mid)}


def experiment(modes, a, b, opposite):
    phase = R(0)
    damping = R(0)
    energy = R(0)
    low_displacements = []
    for j in range(modes + 1):
        w, g = mode(j)
        parity = (-1)**j if opposite else 1
        phase += 4 * scale**2 * g**2 * parity * (
            iv.sin(w*a) + iv.sin(w*b) - iv.sin(w*(a+b))) / w**2
        # Interaction-picture displacement, in the B interval, sans lambda.
        re = g * parity * (iv.cos(w*a) - iv.cos(w*(a+b))) / w
        im = g * parity * (iv.sin(w*a) - iv.sin(w*(a+b))) / w
        damping += 4 * scale**2 * g**2 * (1 - iv.cos(w*b)) / w**2
        if j <= 1:
            low_displacements.append((re, im))
        energy += 2 * scale**2 * g**2 * (2 - iv.cos(w*a) - iv.cos(w*b)) / w
    (r0,i0),(r1,i1) = low_displacements
    damping += 4*scale**2*occupation*(r0*r0+i0*i0+r1*r1+i1*i1)
    damping += 8*scale**2*correlation*(r0*r1+i0*i1)
    # For j>M, g_j² <= 2*(80/pi)^8/(beta*j^9); sum j^-p <= M^(1-p)/(p-1).
    sq_over_w2 = 2*(80/iv.pi)**8/(10*beta**3*modes**10)
    phase_tail = 12*scale**2*sq_over_w2
    damping_tail = 8*scale**2*sq_over_w2
    energy_tail = 16*scale**2*(80/iv.pi)**8/(9*beta**2*modes**9)
    unit = R([-1,1])
    positive = R([0,1])
    phase_all = phase + unit*phase_tail
    damp_all = damping + positive*damping_tail
    coh = iv.exp(-damp_all)
    return (phase, phase_all, damp_all, coh*iv.sin(phase_all),
            energy + positive*energy_tail, phase_tail)


def main():
    # The two first-mode sums represent different physical cutoffs from total occupation.
    w, g = mode(1)
    assert R(3)/2 in w and R(3)/5 in g
    assert length*(R(1)/2-2*(R(1)/6+R(1)/40)) > R(2)/5
    runs = {}
    for key, a, b, opposite in [
        ("timelike_access",R(2)/3,R(3)/4,False),
        ("spacelike",R(1)/5,R(1)/5,True),
    ]:
        low = experiment(1,a,b,opposite)[0]
        phase, full, damp, y, energy, tail = experiment(160,a,b,opposite)
        if opposite:
            assert 0 in full and low > R("0.0001")
        else:
            assert full > R("0.05") and y > 0 and abs(full-low) > R("0.001")
        assert tail < R("0.0000000001") and damp > 0 and energy > 0
        runs[key] = {k:display(v) for k,v in zip(
            ["two_mode_phase","160_shell_phase","field_phase","damping_exponent",
             "signed_imag_coherence","bare_energy_gain","phase_tail_upper"],
            [low,phase,full,damp,y,energy,tail])}
    print(json.dumps(runs, indent=2))


if __name__ == "__main__":
    main()
