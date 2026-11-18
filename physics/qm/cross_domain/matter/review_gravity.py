"""从散射四动量、截面曲率和连续性方程分别核对 gravity 的软定理与迹异常。"""
import hashlib
import json
import platform
import subprocess
import sys
from itertools import combinations
from pathlib import Path

import sympy as sp

HERE = Path(__file__).resolve().parent
GRAVITY = HERE.parent / "gravity"
metric = sp.diag(-1, 1, 1, 1)
V = sp.Matrix
R = sp.Rational


def elastic_and_inelastic():
    incoming = (V([5, 0, 0, 3]), V([5, 0, 0, -3]))
    outgoing = (V([5, 3, 0, 0]), V([5, -3, 0, 0]))
    assert all((p.T * metric * p)[0] == -16 for p in incoming + outgoing)
    da, db = [b-a for a, b in zip(incoming, outgoing)]
    assert da == -db
    # 固定软光线方向 z，x 和 y 都是合法横向规范参数。
    q = V([1, 0, 0, 1])
    ex, ey = V([0, 1, 0, 0]), V([0, 0, 1, 0])
    def gauge_projection(charges, final, pol):
        assert (q.T * metric * pol)[0] == 0
        eps = metric * (q * pol.T + pol * q.T) * metric
        def leg(p):
            return (p.T * eps * p)[0] / (p.T * metric * q)[0]
        return sum(g*(leg(b)-leg(a)) for g, a, b in zip(charges, incoming, final))
    assert gauge_projection((2, 1), incoming, ex) == 0
    assert gauge_projection((2, 1), outgoing, ey) == 0
    exposed = gauge_projection((2, 1), outgoing, ex)
    assert exposed == 6 and gauge_projection((1, 1), outgoing, ex) == 0
    # 一个三体硬事件，每条腿均换动量；每种交换都沿 x，约束秩只有 1。
    initial = [V([5, -1, 2, 0]), V([5, -1, -2, 0]), V([5, 2, 0, 1])]
    final = [V([p[0], -p[1], p[2], p[3]]) for p in initial]
    assert all((p.T * metric * p)[0] == -20 for p in initial + final)
    transfers = sp.Matrix.hstack(*(b-a for a, b in zip(initial, final)))
    assert transfers.rank() == 1 and transfers * V([1, 3, 2]) == sp.zeros(4, 1)
    assert transfers * sp.ones(3, 1) == sp.zeros(4, 1)
    # 处在不同交换分量的两对物种，随后增加一条真正的跨分量非前向弹性边。
    isolated = V([[1, -1, 0, 0], [0, 0, 1, -1]])
    connected = isolated.col_join(V([[0, 1, -1, 0]]))
    assigned = V([1, 1, 3, 3])
    assert isolated * assigned == sp.zeros(2, 1)
    assert connected.nullspace() == [sp.ones(4, 1)] and (connected*assigned)[2] == -2
    return dict(forward_bad_charge=0, single_blind_polarization=0,
                revealing_polarization=int(exposed), three_body_rank=transfers.rank(),
                three_body_charges=[1, 3, 2], three_body_x_transfers=[int(x) for x in transfers.row(1)],
                disconnected_nullity=4-isolated.rank(), connected_nullity=4-connected.rank())


def other_interactions():
    source, a, b = R(1, 5), R(1, 4), -R(1, 4)
    acc_a, acc_b = 1+2*source*a, 1+2*source*b
    eta = 2*(acc_a-acc_b)/(acc_a+acc_b)
    assert eta == R(1, 5)
    # 线性潮汐场 R_0x0x，作用在可定向的四极矩上。q 为下指标。
    w = sp.symbols("omega", positive=True)
    q = V([-w, 0, 0, w])
    xi = V(sp.symbols("xi0:4"))
    def tidal(q, eps):
        return (q[0]**2*eps[1, 1] + q[1]**2*eps[0, 0] - 2*q[0]*q[1]*eps[0, 1])/2
    gauge = q * xi.T + xi * q.T
    assert tidal(q, gauge).expand() == 0
    tt = sp.diag(0, 1, -1, 0)
    correction = tidal(q, tt)
    assert sp.limit(w*correction, w, 0) == 0 and correction.subs(w, R(1, 5)) == R(1, 50)
    return dict(scalar_accelerations=[str(acc_a), str(acc_b)], scalar_eta=str(eta),
                extra_TT_tidal_vertex=str(correction), tidal_at_one_fifth="1/50",
                tidal_pure_gauge=0, extra_leading_residue=0)


def invariants(sections):
    # 正交标架截面曲率 K_ab 已包含时间方向的符号；平方收缩的符号相消。
    planes = list(combinations(range(4), 2))
    ric_eig = [sum(k for pair, k in zip(planes, sections) if i in pair) for i in range(4)]
    scalar, ric2 = sum(ric_eig), sum(x*x for x in ric_eig)
    riem2 = 4*sum(k*k for k in sections)
    # 逐个截面剥去 Ricci，重构 Weyl 平方，与 Euler 的展开路径不同。
    weyl2 = 4*sum((k - (ric_eig[i]+ric_eig[j])/2 + scalar/6)**2
                  for (i, j), k in zip(planes, sections))
    euler = riem2 - 4*ric2 + scalar**2
    assert sp.expand(3*weyl2-euler - 2*(riem2-ric2)) == 0
    return [sp.simplify(x) for x in (weyl2, euler, riem2, ric2)]


def anomaly():
    h = sp.symbols("H", positive=True)
    ds = invariants([h*h]*6)
    assert ds == [0, 24*h**4, 24*h**4, 36*h**4]
    # dS2(k=1) x S2(k=2) 的两个内部截面非零；输出以 5760 pi^2/N 缩放。
    product = invariants(list(map(sp.Integer, [1, 0, 0, 0, 0, 2])))
    w2, e4, _, _ = product
    correct, missing_weyl = 3*w2-e4, -e4
    assert correct == 20 and missing_weyl == -16
    t, beta, C = sp.symbols("t beta C", positive=True)
    a = t**2
    H = sp.diff(a,t)/a
    time_plane = sp.diff(H,t) + H**2
    flat = invariants([time_plane]*3 + [H**2]*3)
    trace = -beta*flat[1]/6
    scalar = 6*(time_plane+H**2)
    box_r = -(sp.diff(scalar,t,2)+3*H*sp.diff(scalar,t))
    assert flat[0] == 0 and sp.simplify(t**4*box_r) == 216
    assert sp.simplify(t**4*trace/beta) == -32
    # 从迹和连续性积分：d(a^4 rho)/dt = -a^4 H T。
    rho = sp.simplify((sp.integrate(-a**4*H*trace,t)+C)/a**4)
    p = (trace+rho)/3
    assert sp.simplify(rho - 16*beta/t**4-C/t**8) == 0
    assert sp.simplify(sp.diff(rho,t)+3*H*(rho+p)) == 0
    # 在同一 de Sitter 度规加入独立辐射，迹检验与守恒都过，空间方程出现残差。
    rad = C*sp.exp(-4*h*t)
    assert -rad+3*rad/3 == 0 and sp.diff(rad,t)+3*h*(rad+rad/3) == 0
    ray = sp.simplify((rad+rad/3)/rad)
    assert ray == R(4,3)
    return dict(de_sitter_W2_E4_Riem2_Ric2_over_H4=[str(sp.simplify(v/h**4)) for v in ds],
                product_W2_E4_Riem2_Ric2=list(map(int, product)),
                product_scaled_trace=int(correct), product_scaled_trace_without_W2=int(missing_weyl),
                power_law_box_R_times_t4=216, power_law_trace_times_t4_over_beta=-32,
                reconstructed_density=str(rho), dS_radiation_enthalpy_over_radiation=str(ray))


def main():
    if not __debug__:
        raise RuntimeError("必须启用断言")
    inputs = ["GRAVITY.md", "verify_gravity.py", "observed.json"]
    hashes = {s:hashlib.sha256((GRAVITY/s).read_bytes()).hexdigest() for s in inputs}
    independent = dict(ward=elastic_and_inelastic(), interactions=other_interactions(), anomaly=anomaly())
    original = subprocess.check_output([sys.executable, "-B", str(GRAVITY/"verify_gravity.py")])
    assert original == (GRAVITY/"observed.json").read_bytes()
    assert all(hashes[s] == hashlib.sha256((GRAVITY/s).read_bytes()).hexdigest() for s in inputs)
    print(json.dumps(dict(scientific_baseline="67aa5c4d9a7e77da3f2a74dfb717a711f885cca9",
                          gravity_sha256=hashes, reviewer_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                          python=platform.python_version(), sympy=sp.__version__, original_byte_replay="MATCH",
                          independent=independent), indent=2))


if __name__ == "__main__":
    main()
