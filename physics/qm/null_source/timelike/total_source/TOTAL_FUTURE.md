# Actual memory endpoint and complete future source difference

## 1. Maximal-coherence endpoint

At c=w the actual outputs of PREPARATION.md are
\[
 \varrho_\pm=\rho_\perp\otimes P_0+wP_\pm\otimes I_2,\qquad
 \delta\varrho=\delta\rho_s\otimes I_2/2.
\]
This is a factorization of a SIGNED DIFFERENCE. The individual states
generally remain correlated; their actual memory marginal is
(1-w)P0+wP1, not I2/2. The full trace distance is 2w.

For general 0<c<w the complete difference contains an additional term:
\[
 \delta\varrho=c\sigma_z\otimes I
       +\sqrt{c(w-c)}\,\sigma_y\otimes\sigma_y,\quad
 D_{\rm tr}(\varrho_+,\varrho_-)=2\sqrt{wc}.
\]
The two summands anticommute and their square is wc I. Thus the shell
distance 2c is not a bound on every possible full-apparatus record.
The endpoint removes this extra term without an assumed environment reset.

## 2. Prescribed future propagation, allowing nonzero memory stress

In this section take the maximal-coherence endpoint c=w. Start at a common
postpreparation Cauchy surface with these actual outputs.
Assume the same future theory, no direct shell-memory recoupling,
U_g=U_s,g tensor U_m,g, and
T_total=T_s tensor I+I tensor T_m. The memory may have nonzero stress.

Common linear free shell propagation preserves W2 equality, so
Tr(delta rho_s T_s)=0 on each prescribed geometry.
Tr(delta rho_s)=0 then kills memory-only difference terms; the shell mean
identity kills both shell-memory stress cross differences. Therefore
\[
 \delta\langle T_{\rm total}\rangle=0,\qquad
                \Delta N_{\rm total}=\Delta N_s .
\]
Neither absolute memory noise nor absolute correlations vanish by this
argument. On the original static geometry the right-hand side is the
proven pure-pressure kernel. On a different background it must be propagated
and recomputed, not copied from the static formula.

For two histories, B_s=U_s,-^dagger U_s,+ and similarly B_m, the ALL-ORDER
difference is exactly
\[
 \Delta F_{\rm joint}
       =\Delta F_s\,{\rm Tr}[(I_2/2)B_m].
\]
This does not separately factor each individual F_joint into shell and
actual-memory factors. Higher mixed stress differences can be nonzero and
are included by this formula. The memory factor may vanish, so the bare
full-field witness does not automatically prove a full-apparatus witness.

## 3. The on-shell condition has not disappeared

Equal total means BETWEEN preparations do not make their common total mean
equal to the original bare two-field mean. Adding a real memory/carrier may
change the common Einstein background, constraints, counterterms and
retarded response P_total. Thus the old A, P and K0 cannot be used for the
expanded model without a new common mean/constraint/response calculation.

The gate-era controller, timing and program are also outside this future
endpoint theorem. An unmodelled apparatus cannot simply be called an
identical independent rest. The future statement is a useful closed
conditional result, not an on-shell preparation history.
