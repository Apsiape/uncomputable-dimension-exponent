"""Print consolidated markdown tables from out/results_N*.json (for the report)."""
import os
import re
import json
from collections import OrderedDict

OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "out")
NS = (4, 6, 8)


def group_key(name):
    pats = [
        (r"^\(10\) B_\d+L-B_\d+$", "(10) B_e L - B_e, every e < N/2"),
        (r"^\(10\) B_\d+R-", "(10) B_e R - 2^-e B_e, every e < N/2"),
        (r"^\(12\) C_\d+Z", "(12) C_k Z - C_k D_k, every k < N"),
        (r"^\(13\) r\d", "(13) r_i - z_i - (1/2)(I - z_i) s_i, i = 1,2,3"),
        (r"^\(13\) z\d\^2", "domain: z_i projections"),
        (r"^\(14\)", "(14) Z W - Z Init(W), all 23 W (20 controls, 3 counters)"),
        (r"^\(15\)", "(15) U*WU - Z+ Init(W) - (I-Z+) Step(W), all 23 W"),
        (r"^q_.*\^2-q_", "domain: q_sigma projections"),
        (r"^sum_sigma", "domain: sum_sigma q_sigma = I"),
        (r"^2\.5a", "2.5: L,R,F pairwise, with A_a, with all fuel/time clock vars incl. U"),
        (r"^2\.5b", "2.5: Z + workspace pairwise, and with A_a,A_f,A_t,L,R,F"),
        (r"^2\.5c", "2.5: address set {A_a,P_a,T_a,X_a,V,H} with fuel and time sets"),
        (r"clocks commute", "(3): fuel set with time set"),
        (r"^4 \[", "Sec. 4: B,C,Q,Y with A_a and all fuel/time clock vars"),
        (r"^(T_a|X_a|T_f|X_f|T_t|X_t|V|U|Y)\*?(T_a|X_a|T_f|X_f|T_t|X_t|V|U|Y)\*?-I$", "domain: unitarity (W*W = WW* = I)"),
        (r"^(X_a|X_f|X_t|Y)\^2-I$|^(X_a|X_f|X_t|Y)-(X_a|X_f|X_t|Y)\*$|^\(23\) Y\^2-I$", "domain: self-adjoint involutions X_a,X_f,X_t,Y"),
        (r"^P_[aft]\^2-P_|^\(7\) L\^2-L$|^\(11\) Z\^2-Z$|^Q\^2-Q$|^F\^2-F$", "domain: projections P_a,P_f,P_t,L,Z,Q,F"),
    ]
    for p, g in pats:
        if re.search(p, name):
            return g
    return name


def load():
    return {N: json.load(open(os.path.join(OUT, f"results_N{N}.json"))) for N in NS}


def fmtx(v):
    if v is None:
        return "-"
    if v == 0:
        return "0"
    return f"{v:.4g}"


def consolidated(data):
    groups = OrderedDict()
    for N in NS:
        for r in data[N]["rows"]:
            g = group_key(r["name"])
            groups.setdefault(g, {})
            d = groups[g].setdefault(N, dict(n=0, op=0.0, hs=0.0, claim=set(), allpass=True))
            d["n"] += 1
            d["op"] = max(d["op"], r["op_x4N"] or 0.0)
            d["hs"] = max(d["hs"], r["hs_x4N"])
            d["claim"].add(r["claim"] if isinstance(r["claim"], str) else f"<= {r['claim']:.4g}")
            d["allpass"] &= r["status"].startswith("PASS")
    lines = ["| relation (or family) | claimed | # N=4/6/8 | N=4 op*4^N | N=4 HS*4^N | N=6 op*4^N | N=6 HS*4^N | N=8 op*4^N | N=8 HS*4^N | all pass |",
             "|---|---|---|---|---|---|---|---|---|---|"]
    for g, per in groups.items():
        claim = "/".join(sorted(set().union(*[per[N]["claim"] for N in NS if N in per])))
        ns = "/".join(str(per[N]["n"]) if N in per else "0" for N in NS)
        cells = []
        for N in NS:
            if N in per:
                cells += [fmtx(per[N]["op"]), fmtx(per[N]["hs"])]
            else:
                cells += ["-", "-"]
        ok = all(per[N]["allpass"] for N in NS if N in per)
        lines.append(f"| {g} | {claim} | {ns} | " + " | ".join(cells) + f" | {'yes' if ok else 'NO'} |")
    return "\n".join(lines)


def nonzero(data):
    lines = ["| N | relation | op-norm | op*4^N | flat HS | nnz | op-norm method | largest-defect basis states |",
             "|---|---|---|---|---|---|---|---|"]
    for N in NS:
        for r in data[N]["rows"]:
            if r["nnz"] > 0:
                top = "; ".join(f"{s}" for v, s in r["top"][:2])
                lines.append(f"| {N} | {r['name']} | {r['opnorm']:.6e} | {r['op_x4N']:.6g} | {r['hs_flat']:.4e} | "
                             f"{r['nnz']} | {r['op_method'].split(';')[0]} | {top} |")
    return "\n".join(lines)


def dims(data):
    lines = ["| N | K_N | theta_N | max window | k_N | N theta_N | k_N - N theta_N | log2 dim = 3N + k_N | (3+theta_N) N | V order | basis states (x,q,t) with q_halt=1 | q_halt<=F violations |",
             "|---|---|---|---|---|---|---|---|---|---|---|---|"]
    for N in NS:
        f = data[N]["facts"]
        lines.append(f"| {N} | {f['KN']} | {f['thetaN']} | {f['wmax']} | {f['k']} | {f['N_theta']:.4g} | "
                     f"{f['k']-f['N_theta']:.4g} | {f['log2dim']} | {f['claimed_log2dim_leading']:.4g} | {f['Vorder']} | "
                     f"{f['qhalt_basis_states_xqt']} | {f['qhalt_le_F_violations']} |")
    return "\n".join(lines)


if __name__ == "__main__":
    d = load()
    print("## dims\n" + dims(d) + "\n\n## consolidated\n" + consolidated(d) + "\n\n## nonzero\n" + nonzero(d))
    for N in NS:
        print(N, "series", d[N]["series"], "positivity", d[N]["facts"]["positivity"])
        if "fullspace_mismatches" in d[N]:
            print(N, "fullspace mismatches", d[N]["fullspace_mismatches"], d[N]["fullspace_seconds"])
