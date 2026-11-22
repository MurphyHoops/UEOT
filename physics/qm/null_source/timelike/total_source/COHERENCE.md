# A positive finite-shell coherence at unchanged full two-point function

The original two fields and all source parameters are retained. On the k=2
shell omega=sqrt(3), d=4, so there are eight oscillators. Their frozen thermal
occupation is n, q=n/(1+n), and the weight of every total-number-two vector is
\[
                 w=(1-q)^8q^2={n^2\over(1+n)^{10}}.
\]
In a real orthonormal harmonic basis put
\[
 |A_i\rangle=d^{-1/2}\sum_{m=1}^d|2_m\ {\rm in\ species}\ i\rangle,\quad
 K=|A_1\rangle\langle A_2|.
\]
For 0<c<=w define the full shell states
\[
                 \rho_\pm=\rho_{\rm th}\pm c(K+K^\dagger).
\]
The two affected eigenvalues are w+c,w-c; all other eigenvalues stay thermal.
Thus these are normalized positive normal states, not formal covariance
assignments. The main preparation below uses the endpoint c=w.

Both vectors have the same total energy, so the complete total-Hamiltonian
spectral law is unchanged. The shell states are stationary for the static free
Hamiltonian, but in general not KMS. Each species' entire k=2 shell marginal remains
the original thermal marginal. Any operator of degree <=2 in all field
creation/annihilation operators has zero matrix element between A1 and A2:
connecting them requires two annihilations in one species AND two creations
in the other. Hence the complete spacetime two-point function, canonical
commutators, all mean local RSET components, the common mean response/contact
terms and the original exact static mean geometry are identical. Finite-mode
finite-rank changes preserve the Hadamard singularity and all finite moments.

The normalized sum over a full real harmonic multiplet makes each Ai
spatially invariant. These states are not an example of the old angular
internal-rotation exit: their O(2) twirls differ. With
A+=(A1+A2)/sqrt(2), A-=(A1-A2)/sqrt(2) and
B=d^(-1/2) sum a1m^dagger a2m^dagger|0>, the invariant twirl is
\[
 {\cal T}_{O(2)}(K+K^\dagger)
       =P_{A+}-\tfrac12(P_{A-}+P_B)\ne0 .
\]
A common twirl preserves total invariant stress records, but need not keep
the individual species marginals thermal; we do not use it as the main state.

The exact finite-support Fock check uses creation/annihilation on tuples
without a numerical occupation cutoff. It verifies every linear and
quadratic connecting matrix element, total number, and the nonzero quartic
matrix element. The infinite thermal part is handled by its exact geometric
weights, not approximated by this finite support.

A state definition is not yet its autonomous physical preparation. The entropy,
memory, control and total-source responsibilities are treated in PREPARATION.md
and TOTAL_FUTURE.md.
