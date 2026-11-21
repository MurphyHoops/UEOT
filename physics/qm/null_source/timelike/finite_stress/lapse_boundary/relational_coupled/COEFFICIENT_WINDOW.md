# 完整关系算子的实际系数与有限正型窗口

## 1. 从已验收action逐项化简

记H_K=sum(1/k,k=1..K)，C(u)=19+15ell0+30u，
g_K=C/120-H_K/4，ell0=log(A²/4)+2EulerGamma，a=Ae^u。
原ACTION_LIFT中的有限和有闭式
\[
 B_K=-{K(K+1)+H_K\over4},\qquad
 C_{{rad},K}={K(K+1)[K(K+1)-1]\over4}-{H_K\over8}.
\]
将L_ct写为g_Kχ²/2+A_Kχ+L_ct,0，则
\[
 L_{ct,0}=b_0+b_2\kappa^2+b_4\kappa^4,\quad
 b_0={u\over8}+c_{an}+C_{rad,K},\quad
 b_2=g_K-{K(K+1)\over4}-{29\over120},\quad
 b_4={g_K\over2}-{59\over720}.
\]
因此去source connection后的原R5几何势确为
\[
 {d_0\over\kappa}+d_1\kappa+d_3\kappa^3,\qquad
 d_0=V_0a^4U_0-{3V_0a^2\over2}-b_0,\quad
 d_1={3V_0a^2\over2}-g_K+{K(K+1)\over4}+{29\over120},\quad
 d_3={59\over720}-{g_K\over2}.                         \tag{C1}
\]
当前分支U0=0。没有删除零模、真空常数或固定AE反项。

## 2. 实际冻结输入给非空窗口

只读取已验收joint_history/history.json的unfiltered A区间。
选择K=65536、clock patch J=[-1/100,1/100]，有
\[
 .0377337689<g_K(u)<.0427338873,\qquad
 .0605775008<d_3(u)<.0630775600,\quad d_1(u)>0.
\]
故0<g_K<59/360对整个J成立。上一轮quiet-U的|u|<e^-1158
落在该patch中；这不证明新量子态均值沿quiet-U运动。
J是关系时钟变量u的区间，不能标作固有时间或秒。

计算采用调和数Euler–Maclaurin带符号余项：
\[
 H_K=\log K+\gamma+{1\over2K}-{1\over12K^2}
            +{1\over120K^4}+r_K,\quad
 -{1\over252K^6}<r_K<0.
\]
这是完全单调Stieltjes余项的标准调和数界；也可由
Binet积分展开1/(e^t-1)并对剩余项保号得到。
脚本以高精度外向区间运算验证实际参数与相邻负对照，不重求A或模式。
有限K选择是本候选的调节输入，未由Core或自然选择原则导出。

## 3. 两个不能偷换的负对照

K=32768在J上g>0但d3<0。取x平移到R→∞的单位范数固定宽度
几何波包和一个固定有限source能量向量，d3κ³=(9d3/4)x²使完整
moving-frame二次型趋于-∞；其余最高为x^(2/3)，源项x^(-2/3)，
几何导数项有界。因此g>0本身不保证半有界。

K=131072在J上g<0。取支撑远离0的几何波包乘e^(inx)，source固定；
负几何动能随-n²趋于-∞，而其余期望有界。因此下一页的正型证明不覆盖它。
两条结论均不排除别的自伴实现或单位ary演化。

g_K(u)随K严格下降，g_{K+1}-g_K=-1/[4(K+1)]，并趋于-∞。
所以任何保持当前参数与J的正型K窗口都是有限的。
本页K=65536的成功不能当作K→∞的全场闭合。

## 4. 验证等级

精确系数代数、调和数外向界与实际正负符号由脚本检查；
平移/高频试探向量的半有界否定由本页解析证明承担。
没有构造巨大的模式矩阵，也没有把有限模数误称可实验实施。
