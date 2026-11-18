"""Independent common-interface checks. Does not read the QSO holdout."""
import hashlib
import importlib.util
import subprocess
import sys
import json
from pathlib import Path

import mpmath as mp
import sympy as s

HERE = Path(__file__).resolve().parent
COSMO = HERE.parent / "cosmology"


def background_limit():
    # x = H^2; m and r absorb 8 pi G/3 in dust and radiation densities.
    a, ell, k, m, r = s.symbols("a L k m r", positive=True)
    source = ell + m/a**3 + r/a**4
    x = 2*source/(1+s.sqrt(1-4*k*source))
    assert s.simplify(x - k*x**2 - source) == 0
    # Time derivative of the 00 equation; Hdot = a (dx/da)/2.
    hdot = a*s.diff(x,a)/2
    assert s.simplify(2*(1-2*k*x)*hdot + 3*m/a**3 + 4*r/a**4) == 0
    dust = x.subs({k:0,r:0})
    assert dust == ell + m/a**3 and dust.subs(m,0) == ell
    assert (a*s.diff(dust,a)/2).simplify() == -3*m/(2*a**3)
    assert a*s.diff(r/a**4,a) == -4*r/a**4
    return {"low_branch_classical_dust_Lambda":str(dust),
            "empty_classical_limit":str(dust.subs(m,0)),
            "geometric_evolution_identity_residual":"0"}


def eds():
    a = s.symbols("a", positive=True)
    def prime(f):
        return a*s.diff(f,a)

    density, H = a**-3, a**(-s.Rational(3,2))
    assert prime(density) == -3*density and H**2 == density
    for D in (a, a**(-s.Rational(3,2))):
        theta = -prime(D)
        assert (prime(D)+theta).simplify() == 0
        assert (prime(theta)+(2+prime(H)/H)*theta+3*D/2).simplify() == 0
        assert (prime(prime(D))+(2+prime(H)/H)*prime(D)-3*D/2).simplify() == 0
    # Equal background enthalpies, two independent pressureless components.
    # Their compensated decaying relative velocity satisfies the Euler equations.
    theta1, theta2 = a**(-s.Rational(1,2)), -a**(-s.Rational(1,2))
    delta1, delta2 = 2*theta1, 2*theta2
    for theta,delta in [(theta1,delta1),(theta2,delta2)]:
        assert prime(delta)+theta == 0 and prime(theta)+theta/2 == 0
    assert (delta1+delta2)/2 == 0 and (theta1+theta2)/2 == 0 and theta1.subs(a,1) == 1
    return {"growth_indices":["1","-3/2"], "compensated_mode_at_a1":
            {"tracer_theta_per_unit_amplitude":1,"total_theta":0,"total_density_contrast":0}}


def raw_growth(a, om):
    # Exact flat dust + Lambda growing solution, normalized to a at early time.
    z = -(1-om)*a**3/om
    return a*mp.hyp2f1(mp.mpf(1)/3,1,mp.mpf(11)/6,z)


def reference(cal):
    om = mp.mpf(str(cal["candidate"]["Omega_m0"]))
    zs = [cal["6dFGS"]["z"], cal["target"]["z"]]
    result = []
    for z in zs:
        a = 1/(1+mp.mpf(str(z)))
        def D(x):
            return raw_growth(x,om)/raw_growth(1,om)
        value = D(a)
        first = a*mp.diff(D,a)
        second = a*a*mp.diff(D,a,2)+first
        matter_fraction = om/(om+(1-om)*a**3)
        residual = second+(2-3*matter_fraction/2)*first-3*matter_fraction*value/2
        assert abs(residual) < mp.mpf("1e-45")
        assert raw_growth(a,1)==a
        result.append(dict(z=z, D=float(value), f=float(first/value), fD=float(first),
                           growth_equation_residual=float(residual),
                           incorrect_total_contrast_log_growth=float(first/value-3*(1-matter_fraction))))
    fs8 = cal["6dFGS"]["fsigma8"]*result[1]["fD"]/result[0]["fD"]
    return dict(growth=result, fsigma8_at_target_before_any_fiducial_remapping=fs8)


def digest(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def compare_implementation(cal, ref):
    path = COSMO/"replay.py"
    spec = importlib.util.spec_from_file_location("reviewed_cosmology", path)
    model = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(model)
    observed = json.loads(subprocess.check_output([sys.executable, "-B", str(path), "--predict-only"]))
    assert observed["calibration_sha256"] == digest(COSMO/"calibration.json")
    prediction = observed["prediction"]
    archived = json.loads((COSMO/"observed.json").read_bytes())["prediction"]

    eds_growth = model.growth_ode(1.)
    candidate_growth = model.growth_ode(cal["candidate"]["Omega_m0"])
    errors, eds_errors, distance_errors = [], [], []
    for row in ref["growth"]:
        z = row["z"]
        a = 1/(1+z)
        D, DN = candidate_growth(a)
        errors.extend([abs(D-row["D"]), abs(DN-row["fD"])])
        eds_errors.extend(abs(v-a) for v in eds_growth(a))
        distance_errors.append(abs(model.x(z, 1.)-2*(1-(1+z)**-.5)))
        assert abs(model.e(z, 1.)-(1+z)**1.5) < 1e-12
    reference_fs8 = ref["fsigma8_at_target_before_any_fiducial_remapping"]
    assert prediction["order"][-1] == "fsigma8"
    pred_fs8 = prediction["predicted"][-1]
    assert abs(reference_fs8-pred_fs8) < 1e-10
    assert abs(archived["predicted"][-1]-pred_fs8) < 1e-10
    assert max(errors+eds_errors+distance_errors) < 1e-10
    return dict(replay_sha256=digest(path), cosmology_receipt_sha256=digest(COSMO/"observed.json"),
                EdS_max_growth_or_derivative_error=float(max(eds_errors)),
                EdS_max_comoving_distance_error=max(distance_errors),
                candidate_max_growth_or_derivative_error=float(max(errors)),
                predict_only_fsigma8=pred_fs8, archived_fsigma8=archived["predicted"][-1],
                reference_minus_predict_only=reference_fs8-pred_fs8)


if __name__ == "__main__":
    if not __debug__:
        raise RuntimeError("Enable assertions")
    mp.mp.dps = 60
    source = COSMO/"calibration.json"
    cal = json.loads(source.read_text())
    ref = reference(cal)
    print(json.dumps(dict(status="PASS", background=background_limit(), eds=eds(), reference=ref, comparison=compare_implementation(cal,ref),
                          calibration_sha256=digest(source),
                          cosmology_text_sha256=digest(COSMO/"COSMOLOGY.md"),
                          verifier_sha256=digest(Path(__file__))), indent=2))
