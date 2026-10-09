"""Check that the prism graph state is Scott's hexacode state up to local operations.

A. J. Scott, Phys. Rev. A 69, 052330 (2004), eq. (46), gives the six-qubit hexacode state |H>
by a generator matrix over GF(4). This script builds |H> from that matrix with Scott's own
correspondence to Pauli operators, builds the prism graph state used in `AME62`, checks both are
AME, and searches for single-qubit Clifford operations (and, if needed, a relabelling of the
qubits) taking one to the other. It then applies them to the state vector and checks the overlap
with |H> is 1. Exits 1 if any step fails. Needs numpy. This is a numerical side check, not part of
the Lean proof: `ExistsAME 6 2` needs only the prism state, which `AME62` checks directly.

Run from the repository root: `python checks/hexacode_equivalence.py`.
"""
import itertools
import sys

import numpy as np

n = 6
W, WB = "w", "W"  # ω and ω̄
# Scott eq. (46), rows as printed.
G46 = [
    ["1", "0", "0", "1", W, W],
    ["0", "1", "0", W, "1", W],
    ["0", "0", "1", W, W, "1"],
    [W, "0", "0", W, WB, WB],
    ["0", W, "0", WB, W, WB],
    ["0", "0", W, WB, WB, W],
]
# Scott's correspondence: ω → X, ω̄ → Z, 1 → iXZ (= Y), 0 → I.  As (x, z) bits:
SYM = {"0": (0, 0), W: (1, 0), WB: (0, 1), "1": (1, 1)}
PAULI = {(0, 0): "I", (1, 0): "X", (0, 1): "Z", (1, 1): "Y"}


def vec(row):  # symplectic vector: x bits then z bits
    return tuple(SYM[c][0] for c in row) + tuple(SYM[c][1] for c in row)


def add(u, v):
    return tuple(a ^ b for a, b in zip(u, v))


def comm(u, v):  # symplectic form: 0 iff the Paulis commute
    return sum(u[i] * v[n + i] + u[n + i] * v[i] for i in range(n)) % 2


def weight(v):
    return sum(1 for i in range(n) if v[i] or v[n + i])


def group(gens):
    g = {tuple([0] * 2 * n)}
    for v in gens:
        g |= {add(v, w) for w in g}
    return g


def report(name, gens):
    S = group(gens)
    ok_comm = all(comm(u, v) == 0 for u in gens for v in gens)
    minw = min(weight(v) for v in S if any(v))
    print(f"{name}: {len(S)} elements (rank {len(S).bit_length() - 1}), all commute: {ok_comm}, "
          f"min weight of a non-identity element: {minw}")
    return S


# ---- 1. Scott's stabilizer
H_gens = [vec(r) for r in G46]
print("Scott generators:", [" ".join(PAULI[(v[i], v[n + i])] for i in range(n)) for v in H_gens])
S_H = report("Scott hexacode", H_gens)

# ---- 2. The prism graph state's stabilizer: K_v = X_v Z_{N(v)}
EDGES = [(i, (i + 2) % 6) for i in range(6)] + [(i, i + 3) for i in range(3)]
adj = np.zeros((n, n), dtype=int)
for a, b in EDGES:
    adj[a, b] = adj[b, a] = 1


def graph_gens(A):
    return [tuple(int(i == v) for i in range(n)) + tuple(int(A[v, i]) for i in range(n))
            for v in range(n)]


S_P = report("Prism graph", graph_gens(adj))

# ---- 3. State vectors, and the AME check on both
I2 = np.eye(2); X = np.array([[0, 1], [1, 0]]); Z = np.diag([1, -1]); Y = 1j * X @ Z
MAT = {(0, 0): I2, (1, 0): X, (0, 1): Z, (1, 1): Y}


def op(v):
    m = np.array([[1]])
    for i in range(n):
        m = np.kron(m, MAT[(v[i], v[n + i])])
    return m


def stab_state(gens):
    P = np.eye(2 ** n, dtype=complex)
    for v in gens:
        P = P @ (np.eye(2 ** n) + op(v)) / 2
    w, V = np.linalg.eigh((P + P.conj().T) / 2)
    psi = V[:, np.argmax(w)]
    assert abs(w.max() - 1) < 1e-9 and sum(w > 0.5) == 1
    return psi


def is_ame(psi):
    T = psi.reshape([2] * n)
    worst = 0
    for K in itertools.combinations(range(n), 3):
        rest = [i for i in range(n) if i not in K]
        M = np.transpose(T, list(K) + rest).reshape(8, 8)
        rho = M @ M.conj().T
        worst = max(worst, np.abs(rho - np.eye(8) / 8).max())
    return worst


psiH = stab_state(H_gens)
psiP = np.array([(-1) ** sum(((x >> (5 - a)) & 1) * ((x >> (5 - b)) & 1) for a, b in EDGES)
                 for x in range(64)]) / 8
print(f"Scott |H> AME: max deviation from I/8 over all 20 triples = {is_ame(psiH):.2e}")
print(f"Prism  AME:    max deviation from I/8 over all 20 triples = {is_ame(psiP):.2e}")
print(f"Plain overlap |<H|prism>| (no local operations) = {abs(np.vdot(psiH, psiP)):.4f}")

# ---- 4. Local-Clifford equivalence: find a permutation and per-qubit Clifford mapping
# the prism's stabilizer group onto Scott's.  The six single-qubit symplectic maps (mod Paulis),
# each with a unitary that realises it.
Hd = np.array([[1, 1], [1, -1]]) / np.sqrt(2); Sg = np.diag([1, 1j])
CLIFF = [("I", I2), ("H", Hd), ("S", Sg), ("HS", Hd @ Sg), ("SH", Sg @ Hd), ("HSH", Hd @ Sg @ Hd)]


def sym_of(U):  # how U acts on (x, z) by conjugation, read off numerically
    out = {}
    for b, P in MAT.items():
        Q = U @ P @ U.conj().T
        for b2, P2 in MAT.items():
            for ph in (1, -1, 1j, -1j):
                if np.allclose(Q, ph * P2):
                    out[b] = b2
    return out


CMAPS = [(name, U, sym_of(U)) for name, U in CLIFF]
SH_set = set(S_H)


def apply(perm, choice, v):  # qubit i of the image comes from qubit perm[i]
    x = [0] * n; z = [0] * n
    for i in range(n):
        j = perm[i]
        xb, zb = CMAPS[choice[i]][2][(v[j], v[n + j])]
        x[i], z[i] = xb, zb
    return tuple(x) + tuple(z)


found = None
for perm in itertools.permutations(range(n)):
    for choice in itertools.product(range(6), repeat=n):
        if all(apply(perm, choice, v) in SH_set for v in graph_gens(adj)):
            found = (perm, choice)
            break
    if found:
        break

if not found:
    print("FAIL: no local-Clifford equivalence under any relabelling.")
    sys.exit(1)
else:
    perm, choice = found
    print("Equivalence found. Relabelling (new qubit i <- prism qubit perm[i]):", perm)
    print("Local Clifford on each qubit:", [CMAPS[c][0] for c in choice])
    # Build the explicit unitary and check the states agree, allowing a final Pauli string
    # (Paulis are local) to fix the eigenvalue signs.
    T = psiP.reshape([2] * n)
    Tp = np.transpose(T, list(perm)).reshape(64)
    U = np.array([[1]])
    for c in choice:
        U = np.kron(U, CMAPS[c][1])
    phi = U @ Tp
    best = 0; bestp = None
    for p in itertools.product(range(4), repeat=n):
        Pm = np.array([[1]])
        for k in p:
            Pm = np.kron(Pm, [I2, X, Z, Y][k])
        f = abs(np.vdot(psiH, Pm @ phi))
        if f > best:
            best, bestp = f, p
    print(f"|<H| (Pauli) (local Cliffords) (relabel) |prism>| = {best:.12f}",
          "Pauli fix:", "".join("IXZY"[k] for k in bestp))
    if best < 1 - 1e-9 or is_ame(psiH) > 1e-12 or is_ame(psiP) > 1e-12:
        print("FAIL")
        sys.exit(1)
    print("PASS: the prism graph state is Scott's hexacode state up to local operations.")
