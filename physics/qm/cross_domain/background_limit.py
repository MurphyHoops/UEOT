"""Distance effect of one conformal scalar on the normalized, flat dust background."""
import json
from pathlib import Path

import mpmath as mp

ROOT = Path(__file__).resolve().parent


def main():
    mp.mp.dps = 170
    calibration = json.loads((ROOT / "cosmology/calibration.json").read_text(), parse_float=mp.mpf)
    feedback = json.loads((ROOT / "gravity/observed.json").read_text())["results"]["feedback"]
    assert feedback["rho_over_H4"] == "N/(960*pi**2)"
    candidate = calibration["candidate"]
    matter = candidate["Omega_m0"]
    assert candidate["flat"] and candidate["Omega_Lambda0"] == 1 - matter
    zmax = calibration["target"]["z"]
    # One field, fixed H0 illustration in s^-1; BAO does not separately fix H0 and rd.
    megaparsec_km = (648000 / mp.pi) * 149597870700 * 1000
    hubble = 100 * candidate["h_for_sigma8_convention"] / megaparsec_km
    eta = (mp.mpf("5.391247e-44") * hubble)**2 / (360 * mp.pi)

    def classical(z):
        return 1 + matter * ((1 + z)**3 - 1)

    def shift(z):
        # Factoring the quadratic for u-e avoids subtracting two almost equal roots.
        e = classical(z)
        disc = 1 - 4 * eta * (e - eta)
        assert disc > 0
        return 2 * eta * (e**2 - 1) / (1 - 2 * eta * e + mp.sqrt(disc))

    def hubble_distance_loss(z):
        e = classical(z)
        u = e + shift(z)
        return shift(z) / (mp.sqrt(u * e) * (mp.sqrt(u) + mp.sqrt(e)))

    assert shift(0) == 0
    e = classical(zmax)
    u = e + shift(zmax)
    assert abs((u - e) / (eta * (u**2 - 1)) - 1) < mp.mpf("1e-40")
    distance_loss = mp.quad(hubble_distance_loss, [0, zmax])
    classical_distance = mp.quad(lambda z: 1 / mp.sqrt(classical(z)), [0, zmax])
    errors = (hubble_distance_loss(zmax) * mp.sqrt(e), distance_loss / classical_distance)
    # On the low branch 1<=u<=2e so 0<=(u-e)/e<=4*eta*e. Integrate the same bound.
    bound = 2 * eta * e
    assert all(0 < value < bound for value in errors) and bound < mp.mpf("1.4e-124")
    print(f"z={zmax}, eta={mp.nstr(eta, 6)}, uniform distance bound={mp.nstr(bound, 6)}, "
          f"fractional DH and DM changes={', '.join(mp.nstr(v, 6) for v in errors)} (magnitudes)")


if __name__ == "__main__":
    main()
