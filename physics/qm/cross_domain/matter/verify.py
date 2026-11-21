"""一次复算。--predict-only 在访问留出文件之前返回。所有输入值均为源论文的十进制。"""
import argparse
import cmath
import hashlib
import itertools
import json
import math
from fractions import Fraction as F
from pathlib import Path

from mpmath import iv

HERE = Path(__file__).resolve().parent
iv.dps = 40
# 中心、下误差、上误差；同一论文分别给出的分量按冻结约定取和。
INPUT = {
    "tan12": ("0.2323", "0.0015", "0.0015"),
    "ub_cb": ("0.083", "0.008", "0.008"),
    "cb": ("0.0406", "0.0009", "0.0009"),
    "gamma_deg": ("68.7", "5.1", "5.2"),
    "xi": ("1.206", "0.024", "0.024"),
    "md_MeV": ("5279.58", "0.43", "0.43"),
    "ms_MeV": ("5366.90", "0.51", "0.51"),
    "dm_s_per_ps": ("17.7683", "0.0083", "0.0083"),
}


def exact(x):
    x = F(x)
    return iv.mpf(x.numerator)/x.denominator


def boxes(key, k, pieces=1):
    mid, down, up = map(F, INPUT[key])
    low, high = mid-k*down, mid+k*up
    step = (high-low)/pieces
    return [iv.mpf([exact(low+j*step).a, exact(low+(j+1)*step).b]) for j in range(pieces)]


def ratio_sq(t, r, cb, deg):
    g = deg*iv.pi/180
    c13 = iv.sqrt(1-(r*cb)**2)
    s23 = cb/c13
    c23 = iv.sqrt(1-s23**2)
    h = r*c13*c23
    z = (s23*r*cb/(t*c23))*iv.sin(g)
    cos_delta = iv.cos(g)*iv.sqrt(1-z**2)-iv.sin(g)*z
    cross = 2*t*h*cos_delta
    return (t**2+h**2-cross)/(1+(t*h)**2+cross)


def dyadic(endpoint):
    sign, mantissa, exponent, _ = endpoint
    return (-1)**sign*mantissa*F(2)**exponent


def outward(x, digits=8):
    lo, hi = map(dyadic, x._mpi_)
    scale = 10**digits
    return [(lo*scale).__floor__()/scale,(hi*scale).__ceil__()/scale]


def predict(k):
    # 对每个子箱整段作向外区间运算；分箱减少重复出现同一变量的区间依赖。
    n = 1 if not k else 24
    factors = [boxes("tan12",k),boxes("ub_cb",k,n),boxes("cb",k),boxes("gamma_deg",k,n)]
    ranges = [ratio_sq(*args) for args in itertools.product(*factors)]
    r2 = iv.mpf([min(x.a for x in ranges),max(x.b for x in ranges)])
    md, ms, xi, ds = [boxes(key,k)[0] for key in ("md_MeV","ms_MeV","xi","dm_s_per_ps")]
    dm = ds*(md/ms)*r2/xi**2
    tolerance = iv.mpf([exact(F(49,51)).a,exact(F(51,49)).b])
    return {"abs_Vtd_over_Vts":outward(iv.sqrt(r2)), "dm_d":outward(dm),
            "dm_d_with_2pct_per_amplitude":outward(dm*tolerance)}


def alternatives():
    result = []
    for colors, families, plus in ((3,3,1),(5,5,2)):
        doublets = families*(colors+1)
        anomaly = families + colors*(2*plus-families)
        b_color = F(11*colors,3)-2*families
        b_left = 11-F(doublets,3)-F(3,6)
        up, down = F(colors+1,2*colors), -F(colors-1,2*colors)
        assert up-down==1 and (colors*down).denominator==1
        assert (-1)**doublets==1 and anomaly==0 and min(b_color,b_left)>0
        result.append({"spectrum":[colors,families,plus],"SU2_doublets":doublets,
                       "Witten_sign":(-1)**doublets,"SU3L_cubic":anomaly,
                       "bC_bL":[str(b_color),str(b_left)],"qu_qd":[str(up),str(down)]})
    assert (-1)**(doublets+1)==-1
    return result


def checks():
    t,r,b,g = [float(INPUT[k][0]) for k in ("tan12","ub_cb","cb","gamma_deg")]
    s12,c12=t/math.hypot(1,t),1/math.hypot(1,t)
    s13=r*b
    c13=math.sqrt(1-s13*s13)
    s23=b/c13
    c23=math.sqrt(1-s23*s23)
    gamma=math.radians(g)
    delta=gamma+math.asin(s23*s13*math.sin(gamma)/(t*c23))
    phase=cmath.exp(1j*delta)
    ud,ub,cd,cb=c12*c13,s13/phase,-s12*c23-c12*s23*s13*phase,b
    assert abs(cmath.phase(-ud*ub.conjugate()/(cd*cb))-gamma)<1e-14
    td,ts,tb=s12*s23-c12*c23*s13*phase,-c12*s23-s12*c23*s13*phase,c23*c13
    direct=abs(td/ts)
    assert abs(sum(abs(v)**2 for v in (td,ts,tb))-1)<1e-14
    rlo,rhi=predict(0)["abs_Vtd_over_Vts"]
    assert rlo<=direct<=rhi
    # 仅用于检查 LL 运输与相干求和的自定标样例，以下 alpha_s 不作数据输入。
    u6=(.089/.108)**(2/7)
    u5=(.108/.22)**(6/23)
    # 公用短程系数任取，在相同输入下直接比较干涉前后的模长比。
    amplitudes=[(tb.conjugate()*q)**2*(1.3*u5+.7*u6*u5) for q in (td,ts)]
    assert abs(abs(amplitudes[0]/amplitudes[1])-direct**2)<1e-14
    assert abs(1.3*u5+.7*u6*u5)**2 > (1.3*u5)**2+(.7*u6*u5)**2
    u=(td.conjugate(),ts.conjugate(),tb.conjugate())
    coeff=lambda i,j:(u[i]*u[j].conjugate())**2
    cycle=coeff(0,1)*coeff(1,2)*coeff(2,0)
    assert cycle.real>0 and abs(cycle.imag)<1e-14*cycle.real
    assert (1j*cycle).imag>0   # 第三道增独立相位，零投影失败
    return {"CKM_direct_ratio":direct,"illustrative_LL_U6_U5":[u6,u5],
            "cycle_im_over_abs":cycle.imag/abs(cycle),"cycle_after_extra_i":(1j*cycle).imag/abs(cycle)}


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument("--predict-only",action="store_true")
    args=parser.parse_args()
    result={"freeze_sha256":hashlib.sha256((HERE/"FROZEN.md").read_bytes()).hexdigest(),
            "candidates":alternatives(),"checks":checks(),"prediction":{k:predict(k) for k in (0,1,2)}}
    if not args.predict_only:
        obs=json.loads((HERE/"holdout.json").read_text())
        center,err=F(obs["center"]),sum(map(F,obs["errors"]))
        comparison={}
        for k in (1,2):
            low,high=center-k*err,center+k*err
            comparison[k]={"observed_box":[float(low),float(high)]}
            for name in ("dm_d","dm_d_with_2pct_per_amplitude"):
                a,b=map(lambda x:F(str(x)),result["prediction"][k][name])
                comparison[k][name]="DISJOINT" if b<low or high<a else "OVERLAP"
        result["holdout"]=comparison
        # 正常路径必须能识别一个与模型不相容的留出，而非恒报重叠。
        upper=result["prediction"][2]["dm_d_with_2pct_per_amplitude"][1]
        assert F(str(upper)) < F("0.9")-2*err
    print(json.dumps(result,ensure_ascii=False,indent=2,allow_nan=False))


if __name__=="__main__":
    main()
