"""The flat finite models of Section 7 of the paper, built on basis labels.

Registers: x (address, N bits), q (fuel, N bits), t (time, N bits),
y (optional register, k_N qubits).  Bit j of a register is the j-th binary
digit of its integer value (bit 0 = least significant).

Interpretive choices (defaults = the reading the text supports; the
`opts` dict switches to the alternative readings for the ablation runs):
  rot   : 'up'   T|b> = |b'> with b'_{j+1} = b_j, so T P_j T* = P_{j+1}
                 (the clock of Section 4 of the paper).  'down' = the reverse rotation.
  conj  : 'DTD*' T_a = D (T_0 x I) D*, X_a = D (X_0 x I) D*   (eq. 33 as written)
          'D*TD' the opposite conjugation;  'none' T_a = T_0 x I, X_a = X_0 x I.
  r0    : +1     R_0 moves the content of slot i to slot i+1 (cyclic);
          -1     the reverse.
  addr  : 'lsb'  the integer x that V increments has bit 0 = clock digit P_a
          'msb'  clock digit P_a = the most significant bit of x (ablation).
  time  : 'lsb'  workspace at (x,q,t) is Step^{t mod 2^k}(Init(x)), t read
                 with bit 0 least significant; 'msb' reads t bit-reversed.
  fuel  : 'lead0' k = position of the first zero of q starting from bit 0;
          'top'  first zero scanning from bit N-1 (ablation).
  kdelta: 0      optional register has k_N = 1 + max window qubits (eq. 29);
          -1     one qubit fewer (ablation: is the +1 in (29) needed?).
"""
import numpy as np
from e2_engine import Op, I, ZERO, comm, diag_mono, perm_mono

# ----------------------------------------------------------------------------
# The counter program M (Minsky machine).  Counters c1, c2, c3; counter value
# n is encoded r = 2^-n.  c1 holds the input e; c2 = c3 = 0 initially.
#   e = 0          : halts after 6 steps
#   e = 1          : never halts (state 'loop' increments c3 forever)
#   e >= 2         : sets c2 = 1, multiplies c2 by 4 e times, counts c2 down,
#                    halts.  h(2) = 94, h(3) = 353, h(e) ~ (13/3+1) 4^e.
# ----------------------------------------------------------------------------
PROG = {
    "start": ("DEC", 1, "d1", "z0"),
    "z0": ("INC", 2, "z1"),
    "z1": ("INC", 2, "z2"),
    "z2": ("DEC", 2, "z2", "halt"),
    "d1": ("DEC", 1, "g0", "loop"),
    "loop": ("INC", 3, "loop"),
    "g0": ("INC", 1, "g1"),
    "g1": ("INC", 1, "g2"),
    "g2": ("INC", 2, "mc"),
    "mc": ("DEC", 1, "ma", "cnt"),
    "ma": ("DEC", 2, "mb1", "bk"),
    "mb1": ("INC", 3, "mb2"),
    "mb2": ("INC", 3, "mb3"),
    "mb3": ("INC", 3, "mb4"),
    "mb4": ("INC", 3, "ma"),
    "bk": ("DEC", 3, "bi", "mc"),
    "bi": ("INC", 2, "bk"),
    "cnt": ("DEC", 2, "cnt", "halt"),
    "halt": ("HALT",),
    "idle": ("IDLE",),
}
STATES = list(PROG)
NCTR = 3


def classical_run(e, steps, prog=PROG):
    """Classical simulation (independent of the Step polynomial).
    Returns list of (state, counters) for m = 0..steps-1; counters are ints
    (None = infinite, i.e. r = 0)."""
    st, c = "start", [e, 0, 0]
    out = []
    for _ in range(steps):
        out.append((st, tuple(c)))
        ins = prog[st]
        if ins[0] == "INC":
            c[ins[1] - 1] += 1
            st = ins[2]
        elif ins[0] == "DEC":
            i = ins[1] - 1
            if c[i] is not None and c[i] > 0:
                c[i] -= 1
                st = ins[2]
            else:
                st = ins[3]
    return out


def halting_time(e, cap, prog=PROG):
    st, c = "start", [e, 0, 0]
    for m in range(cap):
        if st == "halt":
            return m
        ins = prog[st]
        if ins[0] == "INC":
            c[ins[1] - 1] += 1
            st = ins[2]
        elif ins[0] == "DEC":
            i = ins[1] - 1
            if c[i] > 0:
                c[i] -= 1
                st = ins[2]
            else:
                st = ins[3]
    return None if st != "halt" else cap


# ----------------------------------------------------------------------------
# helpers
# ----------------------------------------------------------------------------

def rotl(v, n, s=1):
    s %= n
    m = (1 << n) - 1
    return ((v << s) | (v >> (n - s))) & m if s else v


def rotr(v, n, s=1):
    return rotl(v, n, -s)


def bitrev(v, n):
    out = np.zeros_like(v)
    for j in range(n):
        out |= ((v >> j) & 1) << (n - 1 - j)
    return out


def clock_A_table(N):
    v = np.arange(1 << N)
    A = np.zeros(1 << N)
    for j in range(N):
        A += 3.0 * ((v >> j) & 1) * 4.0 ** (-(j + 1))
    return A


def flag_table(N, KN):
    x = np.arange(1 << N)
    f = np.zeros(1 << N, dtype=np.int64)
    for e in KN:
        f += ((x % 4 ** (e + 1)) == 4 ** e).astype(np.int64)
    assert f.max() <= 1
    return f


def window_max(f, N):
    """max_x sum_{j=1}^N f(x-j) on Z/2^N (cyclic)."""
    n = len(f)
    ext = np.concatenate([f, f[:N]])
    cs = np.concatenate([[0], np.cumsum(ext)])
    w = cs[N:N + n] - cs[0:n]  # window starting at x0 of length N
    return int(w.max())


# ----------------------------------------------------------------------------
# the model
# ----------------------------------------------------------------------------

class Model:
    def __init__(self, N, opts=None, prog=PROG):
        assert N % 2 == 0
        self.N = N
        self.o = dict(rot="up", conj="DTD*", r0=+1, addr="lsb", time="lsb", fuel="lead0", kdelta=0)
        if opts:
            self.o.update(opts)
        o = self.o
        self.prog = prog
        n2 = 1 << N
        mask = n2 - 1
        # --- halting set K_N, flags, k_N
        self.htimes = {e: halting_time(e, n2 + 5, prog) for e in range(N // 2)}
        self.KN = [e for e in range(N // 2) if self.htimes[e] is not None and self.htimes[e] < n2]
        self.thetaN = sum(4.0 ** (-(e + 1)) for e in self.KN)
        self.f = flag_table(N, self.KN)
        self.wmax = window_max(self.f, N)
        self.k = 1 + self.wmax + o["kdelta"]  # kdelta != 0 only in the ablation
        k = self.k
        self.bits = dict(x=N, q=N, t=N, y=k)
        self.h = np.concatenate([[0], np.cumsum(self.f)[:-1]])  # h(x) = sum_{r<x} f(r)
        self.Atab = clock_A_table(N)
        x = np.arange(n2)
        # carry coordinate H
        tr1 = np.zeros(n2, dtype=np.int64)  # number of initial (low-order) ones
        for j in range(N):
            tr1 += np.all([((x >> i) & 1) == 1 for i in range(j + 1)], axis=0)
        self.tr1 = tr1
        self.Htab = np.where(tr1 < N, 4.0 ** (-tr1.astype(float)), 0.0)
        # address input decoding: first nonzero base-4 digit
        etab = np.full(n2, -1)
        dig = np.zeros(n2, dtype=np.int64)
        for e in reversed(range(N // 2)):
            d = (x >> (2 * e)) & 3
            etab = np.where(d != 0, e, etab)
            dig = np.where(d != 0, d, dig)
        self.etab, self.digtab = etab, dig
        self.Ltab = ((etab >= 0) & (dig == 1)).astype(float)
        self.Rtab = np.where(etab >= 0, 2.0 ** (-etab.astype(float)), 0.0)
        # fuel first-zero position
        qv = np.arange(n2)
        if o["fuel"] == "lead0":
            self.kq = tr1.copy()  # trailing ones from bit 0 (same function as tr1)
        else:
            self.kq = np.array([_lead_ones_top(v, N) for v in qv])
        # workspace tables: config after m steps from Init(x), m < 2^N
        S = len(STATES)
        self.sidx = {s: i for i, s in enumerate(STATES)}
        ctrl = np.zeros((n2, n2), dtype=np.int64)
        rtab = np.zeros((NCTR, n2, n2))
        for xv in range(n2):
            if self.Ltab[xv] == 1:
                run = classical_run(int(etab[xv]), n2, prog)
                for m, (st, c) in enumerate(run):
                    ctrl[xv, m] = self.sidx[st]
                    for i in range(NCTR):
                        rtab[i, xv, m] = 2.0 ** (-c[i])
            else:
                ctrl[xv, :] = self.sidx["idle"]
                rtab[0, xv, :] = self.Rtab[xv]
                rtab[1, xv, :] = 1.0
                rtab[2, xv, :] = 1.0
        self.ctrl, self.rtab = ctrl, rtab
        self._build_ops()

    # ---------------------------------------------------------------- ops
    def _build_ops(self):
        N, k, o = self.N, self.k, self.o
        n2 = 1 << N
        mask = n2 - 1
        Atab, f, h = self.Atab, self.f, self.h
        up = o["rot"] == "up"
        r0 = o["r0"]

        def T_fwd(v):
            return rotl(v, N) if up else rotr(v, N)

        def T_inv(v):
            return rotr(v, N) if up else rotl(v, N)

        def yrot(y, m):  # R_0^m, m an int array
            m = (r0 * m) % k
            out = y.copy()
            for s in range(1, k):
                sel = m == s
                if sel.any():
                    out[sel] = rotl(y[sel], k, s)
            return out

        def rep(lab, **kw):
            d = dict(lab)
            d.update(kw)
            return d

        ops = {}
        # ---- ordinary clocks on q (fuel) and t (time), and the bare address clock on x
        for r in ("x", "q", "t"):
            ops[f"A0_{r}"] = Op.of(diag_mono(f"A_{r}", r, lambda lab, r=r: Atab[lab[r]]))
            ops[f"P0_{r}"] = Op.of(diag_mono(f"P_{r}", r, lambda lab, r=r: (lab[r] & 1).astype(float)))
            ops[f"T0_{r}"] = Op.of(perm_mono(f"T_{r}", r, lambda lab, r=r: rep(lab, **{r: T_fwd(lab[r])}),
                                             lambda lab, r=r: rep(lab, **{r: T_inv(lab[r])})))
            ops[f"X0_{r}"] = Op.of(perm_mono(f"X_{r}", r, lambda lab, r=r: rep(lab, **{r: lab[r] ^ 1}),
                                             lambda lab, r=r: rep(lab, **{r: lab[r] ^ 1})))
        for r, j in (("q", "f"), ("t", "t")):
            ops[f"A_{j}"], ops[f"P_{j}"] = ops[f"A0_{r}"], ops[f"P0_{r}"]
            ops[f"T_{j}"], ops[f"X_{j}"] = ops[f"T0_{r}"], ops[f"X0_{r}"]

        # ---- address clock with the optional-register coupling
        if o["addr"] == "lsb":
            ops["A_a"], ops["P_a"] = ops["A0_x"], ops["P0_x"]
            T0x, X0x = ops["T0_x"], ops["X0_x"]
            inc = lambda v: (v + 1) & mask
            dec = lambda v: (v - 1) & mask
        else:  # clock digit j = bit N-1-j of the integer x
            ops["A_a"] = Op.of(diag_mono("A_a(msb)", "x", lambda lab: Atab[bitrev(lab["x"], N)]))
            ops["P_a"] = Op.of(diag_mono("P_a(msb)", "x", lambda lab: ((lab["x"] >> (N - 1)) & 1).astype(float)))
            T0x = Op.of(perm_mono("T_x(msb)", "x", lambda lab: rep(lab, x=bitrev(T_fwd(bitrev(lab["x"], N)), N)),
                                  lambda lab: rep(lab, x=bitrev(T_inv(bitrev(lab["x"], N)), N))))
            X0x = Op.of(perm_mono("X_x(msb)", "x", lambda lab: rep(lab, x=lab["x"] ^ (1 << (N - 1))),
                                  lambda lab: rep(lab, x=lab["x"] ^ (1 << (N - 1)))))
            inc = lambda v: (v + 1) & mask
            dec = lambda v: (v - 1) & mask
        D = Op.of(perm_mono("D", "xy", lambda lab: rep(lab, y=yrot(lab["y"], h[lab["x"]])),
                            lambda lab: rep(lab, y=yrot(lab["y"], -h[lab["x"]]))))
        ops["D"] = D
        if o["conj"] == "DTD*":
            ops["T_a"], ops["X_a"] = D * T0x * D.H, D * X0x * D.H
        elif o["conj"] == "D*TD":
            ops["T_a"], ops["X_a"] = D.H * T0x * D, D.H * X0x * D
        else:
            ops["T_a"], ops["X_a"] = T0x, X0x
        ops["V"] = Op.of(perm_mono("V", "xy",
                                   lambda lab: rep(lab, x=inc(lab["x"]), y=yrot(lab["y"], f[lab["x"]])),
                                   lambda lab: rep(lab, x=dec(lab["x"]), y=yrot(lab["y"], -f[dec(lab["x"])]))))
        ops["H"] = Op.of(diag_mono("H", "x", lambda lab: self.Htab[lab["x"]]))
        ops["U"] = Op.of(perm_mono("U", "t", lambda lab: rep(lab, t=(lab["t"] + 1) & mask),
                                   lambda lab: rep(lab, t=(lab["t"] - 1) & mask)))
        # ---- input decoding, flags, conditional clock
        ops["L"] = Op.of(diag_mono("L", "x", lambda lab: self.Ltab[lab["x"]]))
        ops["R"] = Op.of(diag_mono("R", "x", lambda lab: self.Rtab[lab["x"]]))
        ops["F"] = Op.of(diag_mono("F", "x", lambda lab: f[lab["x"]].astype(float)))
        ops["Q"] = Op.of(diag_mono("Q", "xy", lambda lab: (f[lab["x"]] * (lab["y"] & 1)).astype(float)))
        ops["Y"] = Op.of(perm_mono("Y", "xy", lambda lab: rep(lab, y=lab["y"] ^ f[lab["x"]]),
                                   lambda lab: rep(lab, y=lab["y"] ^ f[lab["x"]])))
        self._build_BC(yrot, dec)
        ops["B"] = Op.of(diag_mono("B", "xy", lambda lab: self.Btab[lab["x"], lab["y"]]))
        ops["C"] = Op.of(diag_mono("C", "xy", lambda lab: self.Ctab[lab["x"], lab["y"]]))
        # ---- fuel/time reset and workspace
        kq = self.kq
        tmode = o["time"]

        def mstep(lab):
            t = lab["t"] if tmode == "lsb" else bitrev(lab["t"], N)
            return t & ((1 << kq[lab["q"]]) - 1)

        ops["Z"] = Op.of(diag_mono("Z", "qt", lambda lab: (mstep(lab) == 0).astype(float)))
        ctrl, rtab = self.ctrl, self.rtab
        for s, i in self.sidx.items():
            ops[f"q_{s}"] = Op.of(diag_mono(f"q_{s}", "xqt",
                                            lambda lab, i=i: (ctrl[lab["x"], mstep(lab)] == i).astype(float)))
        for c in range(NCTR):
            rv = lambda lab, c=c: rtab[c, lab["x"], mstep(lab)]
            ops[f"r{c+1}"] = Op.of(diag_mono(f"r{c+1}", "xqt", rv))
            ops[f"z{c+1}"] = Op.of(diag_mono(f"z{c+1}", "xqt", lambda lab, rv=rv: (rv(lab) == 1.0).astype(float)))
            ops[f"s{c+1}"] = Op.of(diag_mono(f"s{c+1}", "xqt",
                                             lambda lab, rv=rv: np.where(rv(lab) == 1.0, 1.0, 2.0 * rv(lab))))
        self.ops = ops

    def _build_BC(self, yrot, dec):
        """B = sum_j 3 Q_j 4^-(j+1), C = sum_j 3 F_j 4^-(j+1), Q_j = V^j Q V^-j,
        computed by iterating V^-1 on labels (independent of the engine)."""
        N, k, f = self.N, self.k, self.f
        n2 = 1 << N
        X, Yy = np.meshgrid(np.arange(n2), np.arange(1 << k), indexing="ij")
        x, y = X.ravel().copy(), Yy.ravel().copy()
        x0, y0 = x.copy(), y.copy()
        # order of V (period of the digit sequences)
        per = None
        Qseq, Fseq = [], []
        j = 0
        while True:
            q = f[x] * (y & 1)
            fl = f[x]
            Qseq.append(q)
            Fseq.append(fl)
            # step V^-1
            xm = dec(x)
            y = yrot(y, -f[xm])
            x = xm
            j += 1
            if np.array_equal(x, x0) and np.array_equal(y, y0):
                per = j
                break
            if j > n2 * k + 2:
                raise RuntimeError("V order not found")
        self.Vorder = per
        self.Qseq = np.array(Qseq)  # (per, n2*2^k): Q_j(s) = Q(V^-j s), periodic in j
        self.Fseq = np.array(Fseq)
        # infinite periodic series, summed far past float precision (4^-70 ~ 1e-42)
        B = np.zeros(x.size)
        C = np.zeros(x.size)
        for jj in reversed(range(70)):  # small terms first
            B += 3.0 * self.Qseq[jj % per] * 4.0 ** (-(jj + 1))
            C += 3.0 * self.Fseq[jj % per] * 4.0 ** (-(jj + 1))
        self.Btab = B.reshape(n2, 1 << k)
        self.Ctab = C.reshape(n2, 1 << k)

    def exact_series_check(self):
        """Exact check of (22) with Python integers:  B(s) = Bn(s)/(4^p - 1),
        Bn(s) = sum_{j<p} 3 Q_j(s) 4^{p-1-j}, p = order of V.  Since
        (V B V*)(s) = B(V^-1 s) and Q_j(V^-1 s) = Q_{j+1}(s), (22) reads
        Bn_shift(s) == 4 Bn(s) - 3 Q(s) (4^p - 1).  Also returns the float
        deviation of Btab from the exact rationals."""
        from fractions import Fraction
        from e2_engine import Space
        p = self.Vorder
        den = 4 ** p - 1
        # V^-1 as a permutation array on the (x,y) basis, taken from the operator V itself
        spc = Space("xy", self.bits)
        lab = spc.labels(0, spc.dim)
        Vm = self.ops["V"].terms[0][1]
        _, lab2 = Vm.adj(lab)          # V^* |s> = |V^-1 s>
        vinv = spc.index(lab2)
        Vm.clear()
        out = {}
        for nm, seq in (("B", self.Qseq), ("C", self.Fseq)):
            S = seq.shape[1]
            nums = []
            for s in range(S):
                num = 0
                for j in range(p):
                    num = num * 4 + 3 * int(seq[j, s])
                nums.append(num)
            tab = (self.Btab if nm == "B" else self.Ctab).ravel()
            bad, maxdev = 0, 0.0
            for s in range(S):
                # (V B V*)(s) = B(V^-1 s) must equal 4B(s) - 3Q(s)
                if nums[vinv[s]] != 4 * nums[s] - 3 * int(seq[0, s]) * den:
                    bad += 1
                maxdev = max(maxdev, abs(float(Fraction(nums[s], den) - Fraction(float(tab[s])))))
            out[nm] = dict(states=S, period=p, exact_failures=bad, float_dev=maxdev)
        return out


def _lead_ones_top(v, N):
    c = 0
    for j in reversed(range(N)):
        if (v >> j) & 1:
            c += 1
        else:
            break
    return c


# ----------------------------------------------------------------------------
# the relation list
# ----------------------------------------------------------------------------

def step_poly(m):
    """Step(W) as a rational polynomial in the workspace variables."""
    ops, prog = m.ops, m.prog
    edges = []  # (selector Op, target, {counter: multiplier})
    for s, ins in prog.items():
        qs = ops[f"q_{s}"]
        if ins[0] == "INC":
            edges.append((qs, ins[2], {ins[1]: 0.5}))
        elif ins[0] == "DEC":
            z = ops[f"z{ins[1]}"]
            edges.append((qs * (I - z), ins[2], {ins[1]: 2.0}))
            edges.append((qs * z, ins[3], {}))
        else:
            edges.append((qs, s, {}))
    step = {}
    for s in prog:
        acc = ZERO
        for sel, tgt, _ in edges:
            if tgt == s:
                acc = acc + sel
        step[f"q_{s}"] = acc
    for c in range(1, NCTR + 1):
        acc = ZERO
        for sel, _, mult in edges:
            acc = acc + sel * (mult.get(c, 1.0) * ops[f"r{c}"])
        step[f"r{c}"] = acc
    return step


def init_poly(m):
    ops = m.ops
    init = {f"q_{s}": ZERO for s in m.prog}
    init["q_start"] = ops["L"]
    init["q_idle"] = I - ops["L"]
    init["r1"] = ops["R"]
    for c in range(2, NCTR + 1):
        init[f"r{c}"] = I
    return init


def relations(m):
    """Yield (name, group, claim, Op).  claim: 'EXACT' or a predicted
    operator-norm bound as a float multiple of 4^-N."""
    o = m.ops
    N = m.N
    out = []
    add = lambda name, grp, claim, op: out.append((name, grp, claim, op))
    # (3) clocks
    for j in ("a", "f", "t"):
        A, P, T, X = o[f"A_{j}"], o[f"P_{j}"], o[f"T_{j}"], o[f"X_{j}"]
        TAT = T * A * T.H
        add(f"(3) [A_{j},P_{j}]", "3 clocks", "EXACT", comm(A, P))
        add(f"(3) T_{j}A_{j}T_{j}*-4A_{j}+3P_{j}", "3 clocks", 3.0, TAT - 4 * A + 3 * P)
        add(f"(3) X_{j}P_{j}X_{j}-(I-P_{j})", "3 clocks", "EXACT", X * P * X - (I - P))
        add(f"(3) [X_{j},T_{j}A_{j}T_{j}*]", "3 clocks", 3.0, comm(X, TAT))
    # (4) guarded increments
    for j, W in (("a", "V"), ("t", "U")):
        A, P, T, X, Wo = o[f"A_{j}"], o[f"P_{j}"], o[f"T_{j}"], o[f"X_{j}"], o[W]
        add(f"(4) guarded increment {W}", "4 guarded inc", np.sqrt(2),
            (Wo - X * ((I - P) + T * Wo * T.H * P)) * (I - A))
    # (5)-(6) carry
    Aa, Pa, Ta, Xa, V, H = o["A_a"], o["P_a"], o["T_a"], o["X_a"], o["V"], o["H"]
    THT = Ta * H * Ta.H
    add("(5) H-(I-P_a)-1/4 P_a T_aHT_a*", "5-6 carry", "EXACT", H - (I - Pa) - 0.25 * Pa * THT)
    add("(5) [P_a,T_aHT_a*]", "5-6 carry", "EXACT", comm(Pa, THT))
    add("(5) [H,A_a]", "5-6 carry", "EXACT", comm(H, Aa))
    add("(6) V*A_aV-A_a+I-7/4H", "5-6 carry", 1.0, V.H * Aa * V - Aa + I - 1.75 * H)
    # (7)-(8)
    Pa1 = Ta * Pa * Ta.H
    E00 = (I - Pa) * (I - Pa1)
    E1 = Pa * (I - Pa1)
    T2, T2i = Ta * Ta, Ta.H * Ta.H
    L, R = o["L"], o["R"]
    add("(7) L-E1-E00 T^2LT^-2", "7-8 L,R", "EXACT", L - E1 - E00 * T2 * L * T2i)
    add("(8) R-(I-E00)-1/2 E00 T^2RT^-2", "7-8 L,R", "EXACT", R - (I - E00) - 0.5 * E00 * T2 * R * T2i)
    add("(7) L^2-L", "domain", "EXACT", L * L - L)
    # (10) consequence
    for e in range(N // 2):
        Be = I
        for jj in range(e):
            Tj, Tji = I, I
            for _ in range(2 * jj):
                Tj, Tji = Tj * Ta, Tji * Ta.H
            Be = Be * (Tj * E00 * Tji)
        Te, Tei = I, I
        for _ in range(2 * e):
            Te, Tei = Te * Ta, Tei * Ta.H
        Be = Be * (Te * E1 * Tei)
        add(f"(10) B_{e}L-B_{e}", "10 consequence", "EXACT", Be * L - Be)
        add(f"(10) B_{e}R-2^-{e}B_{e}", "10 consequence", "EXACT", Be * R - 2.0 ** (-e) * Be)
    # (11)-(12)
    Pf, Pt, Tf, Tt, Z = o["P_f"], o["P_t"], o["T_f"], o["T_t"], o["Z"]
    S = Tf * Tt
    add("(11) Z-(I-P_f)-P_f(I-P_t)SZS*", "11-12 reset", "EXACT", Z - (I - Pf) - Pf * (I - Pt) * S * Z * S.H)
    add("(11) Z^2-Z", "domain", "EXACT", Z * Z - Z)
    Qf = [None] * (N + 1)
    Ptj = [None] * (N + 1)
    Tfp, Ttp = I, I
    for j in range(N):
        Qf[j] = Tfp * Pf * Tfp.H
        Ptj[j] = Ttp * Pt * Ttp.H
        Tfp, Ttp = Tfp * Tf, Ttp * Tt
    for kk in range(N):
        Ck = I
        for j in range(kk):
            Ck = Ck * Qf[j]
        Ck = Ck * (I - Qf[kk])
        Dk = I
        for j in range(kk):
            Dk = Dk * (I - Ptj[j])
        add(f"(12) C_{kk}Z-C_{kk}D_{kk}", "11-12 reset", "EXACT", Ck * Z - Ck * Dk)
    # (13) zero tests
    for c in range(1, NCTR + 1):
        r, z, s = o[f"r{c}"], o[f"z{c}"], o[f"s{c}"]
        add(f"(13) r{c}-z{c}-1/2(I-z{c})s{c}", "13 zero test", "EXACT", r - z - 0.5 * (I - z) * s)
        add(f"(13) z{c}^2-z{c}", "domain", "EXACT", z * z - z)
    # (14)-(15)
    init, step = init_poly(m), step_poly(m)
    U = o["U"]
    Zp = U.H * Z * U
    Wnames = [f"q_{s}" for s in m.prog] + [f"r{c}" for c in range(1, NCTR + 1)]
    for w in Wnames:
        W = o[w]
        add(f"(14) ZW-Z Init(W), W={w}", "14 init", "EXACT", Z * W - Z * init[w])
    for w in Wnames:
        W = o[w]
        add(f"(15) U*WU-Z+Init-(I-Z+)Step, W={w}", "15 step", "EXACT",
            U.H * W * U - Zp * init[w] - (I - Zp) * step[w])
    # control partition
    tot = ZERO
    for s in m.prog:
        tot = tot + o[f"q_{s}"]
        add(f"q_{s}^2-q_{s}", "domain", "EXACT", o[f"q_{s}"] * o[f"q_{s}"] - o[f"q_{s}"])
    add("sum_sigma q_sigma - I", "domain", "EXACT", tot - I)
    # (16)
    F = o["F"]
    add("(16) (I-F) q_halt", "16 halt<=F", "EXACT", (I - F) * o["q_halt"])
    # (21)-(24)
    B, C, Q, Y = o["B"], o["C"], o["Q"], o["Y"]
    add("(21) (I-F)Q  [Q<=F]", "21-24 cond clock", "EXACT", (I - F) * Q)
    for nm, a, b in (("B,Q", B, Q), ("B,F", B, F), ("C,Q", C, Q), ("C,F", C, F), ("B,C", B, C)):
        add(f"(21) [{nm}]", "21-24 cond clock", "EXACT", comm(a, b))
    VBV = V * B * V.H
    add("(22) VBV*-4B+3Q", "21-24 cond clock", "EXACT(series)", VBV - 4 * B + 3 * Q)
    add("(22) VCV*-4C+3F", "21-24 cond clock", "EXACT(series)", V * C * V.H - 4 * C + 3 * F)
    add("(23) YFY-F", "21-24 cond clock", "EXACT", Y * F * Y - F)
    add("(23) YQY-(F-Q)", "21-24 cond clock", "EXACT", Y * Q * Y - (F - Q))
    add("(24) [Y,VBV*]  (est. 32)", "21-24 cond clock", 2.0, comm(Y, VBV))
    add("(24) [Y,C]", "21-24 cond clock", "EXACT", comm(Y, C))
    add("(23) Y^2-I", "domain", "EXACT", Y * Y - I)
    add("Q^2-Q", "domain", "EXACT", Q * Q - Q)
    add("F^2-F", "domain", "EXACT", F * F - F)
    # unitarity / involutions
    for nm in ("T_a", "X_a", "T_f", "X_f", "T_t", "X_t", "V", "U", "Y"):
        Wo = o[nm]
        add(f"{nm}*{nm}-I", "domain", "EXACT", Wo.H * Wo - I)
        add(f"{nm}{nm}*-I", "domain", "EXACT", Wo * Wo.H - I)
    for nm in ("X_a", "X_f", "X_t", "Y"):
        add(f"{nm}^2-I", "domain", "EXACT", o[nm] * o[nm] - I)
        add(f"{nm}-{nm}*", "domain", "EXACT", o[nm] - o[nm].H)
    for j in ("a", "f", "t"):
        add(f"P_{j}^2-P_{j}", "domain", "EXACT", o[f"P_{j}"] * o[f"P_{j}"] - o[f"P_{j}"])
    # Section 2.5 commutations
    fuel = ["A_f", "P_f", "T_f", "X_f"]
    time = ["A_t", "P_t", "T_t", "X_t", "U"]
    addr = ["A_a", "P_a", "T_a", "X_a", "V", "H"]
    LRF = ["L", "R", "F"]
    for i, a in enumerate(LRF):
        for b in LRF[i + 1:]:
            add(f"2.5a [{a},{b}]", "2.5 commutation", "EXACT", comm(o[a], o[b]))
        add(f"2.5a [{a},A_a]", "2.5 commutation", "EXACT", comm(o[a], o["A_a"]))
        for b in fuel + time:
            add(f"2.5a [{a},{b}]", "2.5 commutation", "EXACT", comm(o[a], o[b]))
    work = ["Z"] + Wnames + [f"z{c}" for c in range(1, NCTR + 1)] + [f"s{c}" for c in range(1, NCTR + 1)]
    for i, a in enumerate(work):
        for b in work[i + 1:]:
            add(f"2.5b [{a},{b}]", "2.5 commutation (workspace)", "EXACT", comm(o[a], o[b]))
        for b in ["A_a", "A_f", "A_t", "L", "R", "F"]:
            add(f"2.5b [{a},{b}]", "2.5 commutation (workspace)", "EXACT", comm(o[a], o[b]))
    for a in addr:
        for b in fuel + time:
            add(f"2.5c [{a},{b}]", "2.5 commutation", "EXACT", comm(o[a], o[b]))
    for a in fuel:
        for b in time:
            add(f"(3) [{a},{b}] (clocks commute)", "2.5 commutation", "EXACT", comm(o[a], o[b]))
    # Section 4: B,C,Q,Y commute with A_a and every fuel/time clock variable
    for a in ["B", "C", "Q", "Y"]:
        for b in ["A_a"] + fuel + time:
            add(f"4 [{a},{b}]", "4 commutation", "EXACT", comm(o[a], o[b]))
    return out


def positivity_checks(m):
    """Diagonal positive contractions: spectrum in [0,1]."""
    res = {}
    res["A (clock)"] = (float(m.Atab.min()), float(m.Atab.max()))
    res["H"] = (float(m.Htab.min()), float(m.Htab.max()))
    res["R"] = (float(m.Rtab.min()), float(m.Rtab.max()))
    res["B"] = (float(m.Btab.min()), float(m.Btab.max()))
    res["C"] = (float(m.Ctab.min()), float(m.Ctab.max()))
    for c in range(NCTR):
        res[f"r{c+1}"] = (float(m.rtab[c].min()), float(m.rtab[c].max()))
        s = np.where(m.rtab[c] == 1.0, 1.0, 2.0 * m.rtab[c])
        res[f"s{c+1}"] = (float(s.min()), float(s.max()))
    return res
