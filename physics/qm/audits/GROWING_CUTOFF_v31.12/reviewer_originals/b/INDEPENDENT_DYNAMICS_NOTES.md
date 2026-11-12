# B: independent dynamics notes for interrupted chapter 68

Status: independent reconstruction from the user-supplied handoff. This is not a source audit or a new execution receipt. Exact manuscript and code identities remain to be bound.

## 1. Direct-sum realization and exact growth

Let S = C² tensor l²(N₀), with qubit states g,e, oscillator number N and G=N+|e><e|. Put B=a† sigma_+ + a sigma_-. The mutually orthogonal blocks

E_n = span{|g,n>, |e,n+1>} (n>=0), plus span{|e,0>},

reduce B. On E_n, B=sqrt(n+1) sigma_x; B|e,0>=0. The self-adjoint direct-sum operator has domain

sum_n (n+1)(|c_{g,n}|²+|c_{e,n+1}|²)<infinity.

The finite linear span is a core. Define U_beta through this direct sum, equivalently by the spectral theorem for B. Each block's two G eigenvalues are n and n+2. Therefore, for every finite M,

U_beta Pi_M = Pi_{M+2} U_beta Pi_M.

This remains exact for all real beta; small beta is needed only for the omitted-pulse approximation. Composing any G-filter-preserving operations with L blue pulses produces support within Pi_{N+2L} from Pi_N. In an adaptive finite tree, use the maximum over reachable prefixes or a path-specific carrier followed by a common terminal embedding. Hidden Kraus events must also satisfy their stated growth bounds; averaged energy bounds do not substitute for these identities.

## 2. Complete output and input filtering

For a fixed finite tree including all success, failure, stop and leak outcomes, completion defines a CPTP map to a classical record and quantum terminal state. All reference systems are untouched. Restriction to the growing finite carriers agrees with the original branch products on Pi_N. Contractivity thus transfers the initial projection bound to the full output, uniformly over the declared adaptive controllers.

If t=Tr[(I-Pi_N)rho] and rho_N=Pi_N rho Pi_N/(1-t), then D(rho,rho_N)<=sqrt(t). This concerns a normalized mathematical projection; it does not include physical filter failures.

For the actual projective filter, retain ok/fail in orthogonal classical registers. On fail reset S but retain rho_R^fail=Tr_S[(I-Pi_N)rho(I-Pi_N)]. Against an ideal unfiltered preparation with deterministic ok label, the sharp uniform upper bound is

f(t)=(t+sqrt(4t-3t²))/2,

because the successful block has norm at most sqrt(4t-3t²), and the failure block has norm t. A purification proves the mixed/reference case by contractivity. This bound is increasing on [0,1], so t<=q implies f(t)<=f(q). For pure inputs spanning the accepted/rejected sectors equality is attained. Resetting R is forbidden.

Low-spectrum conditioning preserves the original mean-G upper bound: if p=Tr(Pi_N rho)>0 then Tr(G rho_N)<=Tr(G rho). Indeed each rejected spectral value exceeds each retained spectral value, and the unconditional mean is the convex average of these two conditional means. This conclusion relies on the spectral filter commuting with G; it is not true for an arbitrary projector or heralded operation.

## 3. Omitted-pulse bounds and telescoping

On Pi_M, ||(U_beta-I)Pi_M|| <= min(2, |beta| sqrt(M+1)). Hence for every joint state supported on Pi_M tensor I_R,

D((U_beta tensor I_R)rho(U_beta* tensor I_R),rho) <= min(1, |beta| sqrt(M+1)).

The same statement holds for unnormalized positive inputs after multiplying the bound by their trace. A finer bound uses the largest |exp(±i beta sqrt(n+1))-1| among intersecting blocks; it must include the completed boundary blocks.

For a classical branch tree, replace primitive operations one slot at a time and telescope the complete outputs. Each term is the unnormalized incoming mass in the corresponding hybrid process times its valid pulse bound, followed by CPTP contraction. If record probabilities are independent of the blue pulse and identical across the compared processes, these masses can be evaluated from the common classical source. Otherwise it is invalid to substitute an arbitrary expected number of labels from one model without proving the hybrid relation.

A label-1 count equals physical blue-pulse executions only for a measured-flag/feed-forward implementation. Coherent control may require pulse scheduling in every slot. A mathematical weighted error bound and a hardware pulse-cost claim have different proof obligations.

## 4. Sharp failures

Fixed Pi_N compression loses probability. For |g,N> and a nonzero blue angle, omitted amplitude into |e,N+1> has squared norm sin²(beta sqrt(N+1)); Pi_N U_beta Pi_N is not a deterministic unitary action.

Simultaneous red+blue H=sigma_x(a+a†) does not have finite propagation in number. From a sigma_x eigenstate and oscillator vacuum it produces the coherent state |-i beta>, whose Fock amplitudes exp(-beta²/2)(-i beta)^n/sqrt(n!) are nonzero for all n when beta!=0. Thus exact Pi_{N+2L} closure cannot be transferred to a simultaneous Rabi pulse. The simplified quadrature model alone suffices to refute the generic hard-support implication; it does not assert that all physical Rabi parameter regimes have this exact solution.

Marginal label probabilities of a random-unitary source can be independent of beta. Then labels alone cannot certify |beta|<=beta_max, even if their calibration is arbitrarily precise. Independent phase-sensitive/energy-sensitive calibration or a justified hardware bound remains an input.

## 5. Verification distinctions

These notes establish a paper argument. No Lean theorem, numerical execution, hardware validity, energy-calibration coverage or empirical validation is claimed here. Source comparison, constants and code behavior remain to be audited after the exact interrupted candidate is recovered.
