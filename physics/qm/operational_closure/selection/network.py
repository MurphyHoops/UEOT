"""Renou (E2–E3). P[x-1,z-1,a_index,b,c_index], sign order +,-, b=2*b1+b2."""
import numpy as np

I = np.eye(2)
Z = np.diag([1., -1.])
X = np.array([[0., 1.], [1., 0.]])
J = np.array([[0., -1.], [1., 0.]])
Y = 1j*J
AXES = np.array([Z, X, Y])
PAIRS = [(0, 1), (0, 2), (1, 2)]
CHARLIE = np.array([(AXES[i]+s*AXES[j])/np.sqrt(2)
                    for i, j in PAIRS for s in (1, -1)])
BELLS = np.array([[1,0,0,1], [0,1,1,0], [1,0,0,-1], [0,-1,1,0]])/np.sqrt(2)
BSM = np.einsum('bi,bj->bij', BELLS, BELLS)
IDEAL = np.kron(BSM[0], BSM[0])
SIGNS = np.array([1, -1])
LABELS = ("separable", "real_independent", "complex_independent", "real_shared_reference")


def effects(observables):
    return (np.eye(observables.shape[-1])+SIGNS[None,:,None,None]*observables[:,None])/2


def born(rho, alice, bob, charlie):
    """A,C observables and B's four POVM effects; allows enlarged endpoint registers."""
    da, db, dc = alice.shape[-1], bob.shape[-1], charlie.shape[-1]
    rho = np.asarray(rho)
    if rho.shape != (da*db*dc,)*2 or not np.isfinite(rho).all():
        raise ValueError("state shape or nonfinite entries")
    if (not np.allclose(rho,rho.T.conj(),atol=1e-12,rtol=0)
            or abs(np.trace(rho)-1)>1e-12 or np.linalg.eigvalsh(rho).min() < -1e-12):
        raise ValueError("state must be Hermitian, positive and normalized")
    partial = np.einsum('ijklmn,bmj->bilkn',rho.reshape(da,db,dc,da,db,dc),bob)
    table = np.einsum('xali,zcnk,bilkn->xzabc',effects(alice),effects(charlie),partial,optimize=True)
    if np.abs(table.imag).max()>1e-12:
        raise ValueError("non-real probability")
    return table.real


def probabilities(rho):
    """Complete conditional distribution for the frozen four-qubit measurement menu."""
    return born(rho, AXES, BSM, CHARLIE)


def score(P):
    """Return T and four unnormalized branch contributions T_b in documented Bell order."""
    P = np.asarray(P)
    if (P.shape != (3,6,2,4,2) or not np.isfinite(P).all() or not np.isrealobj(P)
            or P.min() < -1e-12 or np.abs(P.sum(axis=(2,3,4))-1).max()>1e-12):
        raise ValueError("expected 18 normalized real joint distributions")
    S = np.einsum('xzabc,a,c->bxz', P, SIGNS, SIGNS)
    branches = []
    for b, s in enumerate(S):
        z, x = (-1)**(b%2), (-1)**(b//2)
        y = -z*x
        branches.append(z*(s[0,0]+s[0,1]+s[0,2]+s[0,3])
                        +x*(s[1,0]-s[1,1]+s[1,4]+s[1,5])
                        +y*(s[2,2]-s[2,3]+s[2,4]-s[2,5]))
    return float(sum(branches)), list(map(float, branches))


def reference_state(flag):
    # Reorder data A B1 B2 C, extra flags F G into AF B1 B2 CG.
    order = (0,4,1,2,3,5)
    return np.kron(IDEAL,flag).reshape((2,)*12).transpose(order+tuple(i+6 for i in order)).reshape(64,64)


def with_flags(flag):
    def local(obs):
        return np.array([np.kron(m.real,I)+np.kron(m.imag,J) for m in obs])
    return born(reference_state(flag),local(AXES),BSM,local(CHARLIE))


def candidate_tables():
    # A,C always +1; B always 00. Two product sources |00>.
    r = np.zeros((16,16))
    r[0,0] = 1
    always_b00 = np.zeros((4,4,4))
    always_b00[0] = np.eye(4)
    sep = born(r,np.array([I]*3),always_b00,np.array([I]*6))
    # One real CHSH block and two pairs of repeated real observables.
    real = born(IDEAL, np.array([Z,X,Z]), BSM,
                np.array([(Z+X)/np.sqrt(2),(Z-X)/np.sqrt(2),Z,Z,X,X]))
    tau = (np.eye(4)-np.kron(J,J))/4
    return dict(zip(LABELS,(sep,real,probabilities(IDEAL),with_flags(tau))))
