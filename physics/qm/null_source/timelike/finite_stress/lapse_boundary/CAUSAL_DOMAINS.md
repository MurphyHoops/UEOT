# 因果逆进入真实量子源之前：四阶正则工具与全过去 GNS 阻断

本页复用冻结dynamic_inverse的完整静态P、两根、正权谱因子与因果G，
不重新求根、不重跑旧逆/ODE。
新增两个精确接口：完整静态G恢复四阶weighted Sobolev正则；
同一个完整G对实际平稳incoming量子压力的全过去卷积没有GNS L²极限。
它们不等于非静态U上的完整inverse已建成。

## 1. 已冻结的谱输入与记号

\[
 P(s)=(s^2-r_1)(s^2-r_2)F_{\rm spec}(s^2),\quad
 r_1=s_*^2,\ r_2=\sigma_F^2,
\]
\[
 -F_{\rm spec}(y)=c_{\rm spec}
   +\sum_{k\ge2}\mu_k\,{y\over y+b_k},\quad
 c_{\rm spec}>0,\quad b_k=4(k^2-1),\quad\mu_k>0.
\tag{G1}
\]
c_spec不是QUIET_WINDOW的seed c。
原P在开右半平面仅有s*、σF两个简单正实零点，
R=1/P′(σF)≠0，−30<P′(σF)/A<−29。
各k≥3的权重精确为
\[
 \mu_k={2k^2\sqrt{k^2-1}\over
  3\pi^2 A^2(b_k+r_1)(b_k+r_2)};
\]
k=2另有原正thermal项。

## 2. 完整静态逆恢复四阶正则

取γ=24A>σF、c0=1/(60π²A²)。
对k≥10^6，r1<4、r2<10^12、√(k²−1)>k/2，
所以μk>c0/k。原正实部恒等式是
\[
 \operatorname{Re}{-F_{\rm spec}(s^2)\over s}
 \ge {c_{\rm spec}\gamma\over|s|^2},
 \qquad s=\gamma+i\tau.
\]
|τ|≤4γ时直接得|Fspec|≥c_spec/√17。

|τ|≥4γ只需τ>0，负频由共轭对称处理。
取整数band k∈[τ/2−γ/4,τ/2+γ/4]，至少γ/4个，
且k≥10^6（冻结γ区间足够）。逐项有
\[
 b_k\ge3\tau^2/4,\quad
 |\gamma^2-\tau^2+b_k|\le3\gamma\tau/2,\quad
 \operatorname{Im}{s^2\over s^2+b_k}\ge{6\tau\over25\gamma},
\quad \mu_k\ge{16c_0\over9\tau}.
\]
所有项虚部同号，不能相互抵消。故
|Fspec|≥8c0/75>c0/16。
于是整条竖线上
\[
 |F_{\rm spec}((\gamma+i\tau)^2)|\ge
 m_0:=\min(c_{\rm spec}/\sqrt{17},c_0/16)>0.
\tag{G2}
\]
令δj=1−rj/γ²>0，则
\[
 \left|{(\gamma+i\tau)^4\over P(\gamma+i\tau)}\right|
 \le{1\over m_0\delta_1\delta_2}.                    \tag{G3}
\]

定义||f||L²γ=||e^−γt f||L²(R)，
||u||²H⁴γ,γ:=Σ_{j=0}^4 γ^{2(4−j)}||∂t^j u||²L²γ。
对smooth零过去f，冻结因果G的Laplace multiplier为1/P，
Plancherel和|s|≥γ给
\[
 \|G*f\|_{H^4_\gamma,\gamma}\le
 {\sqrt5\over m_0\delta_1\delta_2}\|f\|_{L^2_\gamma}.
\tag{G4}
\]
由稠密延拓得相同有界算子。正γ大于快根，快根并未删除；
这不是无增长权重的稳定性定理。

actual U若要据此构造逆，需要证明(L_U−L_0)G_0在共同prepared域的相对范数。
目前只有RETARDED_RESPONSE的C8→C0尾；不能由G4自动获得所需小范数。

## 3. 将完整G拆出快极点，保留其余响应

现在取中间竖线γm=σF/2>s*。在该线上
|s²−r2|≥|s|²、|s²−r1|≥δ1m|s|²，
δ1m=1−r1/γm²>0。
同一正实部式给
\[
 |1/P(s)|\le[c_{\rm spec}\gamma_m\delta_{1m}|s|^3]^{-1}.
\]
Bromwich积分从右侧移到γm时只跨快极点，横边O(|τ|^−3)消失，
\[
 G(t)=Re^{\sigma_F t}+G_m(t),\quad t\ge0,\qquad
 |G_m(t)|\le C_m e^{\gamma_m t},
\quad C_m={1\over\pi c_{\rm spec}\gamma_m^3\delta_{1m}}.
\tag{G5}
\]
这里R是留数，不是取实部符号。
没有用“只保快pole”的近似代替完整G。

## 4. 每一步都用合法光滑测试

固定非负、单位积分F_out∈C∞_c((0,∞))，令
\[
 Q(s)=(G_R^*F_{\rm out})(s)=\int F_{\rm out}(t)G(t-s)dt.
\]
Q光滑且向未来紧支。对s<0，
Q(s)=R Hσ e^−σs+Qm(s)，Hλ=∫F_out(t)e^λt dt>0，
|Qm(s)|≤Cm Hγm e^−γm s。

选χ∈C∞、非降，χ=0于x≤0、χ=1于x≥δ，δ=1/σF。
对每个有限a<0，
\[
 f_a(s)=\chi(s-a)Q(s)\in C^\infty_c(\mathbb R).
\tag{G6}
\]
因此实际完整source压力p(fa)属于本轮已证明的GNS L²域。
这没有使用尖锐Heaviside起始或尖片方差。

令Ω3=2ω3=4√2，z=σF+iΩ3。
\[
 I_\chi(z)=\int_0^\infty e^{-zx}\chi(x)dx
 ={1\over z}\int_0^\delta e^{-zx}\chi'(x)dx.
\]
χ′非负、积分1，cos(Ω3/σF)>0，所以
\[
 |I_\chi(z)|\ge
 {e^{-1}\cos(\Omega_3/\sigma_F)\over
             \sqrt{\sigma_F^2+\Omega_3^2}}>0.        \tag{G7}
\]
由G5，快项精确积分，余项仅O(e^−γm a)+O(1)，得到
\[
 \lim_{a\to-\infty}e^{(\sigma_F+i\Omega_3)a}
          \widehat f_a(\Omega_3)=R H_\sigma I_\chi(z)\ne0.
\tag{G8}
\]

## 5. 真实高模真空已足够排除全过去 L² 极限

静态incoming薄层源的k=3壳为真空。
TENSOR_NOISE的绝对式在静态给
\[
 \operatorname{Var}p(f_a)
 \ge{32\over V_0^2A^8}|\widehat f_a(\Omega_3)|^2 .
\tag{G9}
\]
这个高模pair输出与所有低模输出正交，因此低模相关不能抵消它。
结合G7/G8，
\[
 \liminf_{a\to-\infty}e^{2\sigma_Fa}\operatorname{Var}p(f_a)
 \ge {32R^2H_\sigma^2\over V_0^2A^8}|I_\chi(z)|^2>0.
\tag{G10}
\]
新证书用|R|>1/(30A)、Hσ>1给明确严格正的保守数值下界表达。
因此该全过去source-only retarded处方没有GNS L²极限。

旧INVERSE已排除慢deterministic forcing的无限过去卷积；
本页新增的是完整静态G和实际平稳量子源的一个明确、平滑、单壳即足够的反例。
它不否定有限准备片响应，也不代替actual U的nonstationary逆证明。
若geometry initial项与source存在真实准备相关，必须连同该项及交叉项重新验收；
本页没有把它们预先调成零或宣称所有joint状态被排除。
