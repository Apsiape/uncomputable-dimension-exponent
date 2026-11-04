import E2.FeasibilityComputation

namespace E2.FeasibilityUniform
noncomputable section
open E2.RealArithmetic E2.FeasibilitySentence E2.FeasibilityComputation Primrec

/-- The finite relevant game table: Alice contexts and answer codes; Bob variable
codes; question probabilities and winning answer/bit pairs. Bounds and proofs
of the original BCSGame are not needed by the sentence-producing algorithm. -/
abbrev Test := ℕ × ℕ × ℚ × List (ℕ × Bool)
abbrev GameCode := List (ℕ × List ℕ) × List ℕ × List Test

def sR (b : Bool) (i j k l : ℕ) : CPoly :=
  cvar (Nat.pair (Encodable.encode b) (2*Nat.pair (Nat.pair i j) (Nat.pair k l)))
def sA (b : Bool) (c a i j : ℕ) : CPoly :=
  cvar (Nat.pair (Encodable.encode b) (2*(2*Nat.pair c (Nat.pair a (Nat.pair i j)))+1))
def sB (b : Bool) (w : ℕ) (a : Bool) (i j : ℕ) : CPoly :=
  cvar (Nat.pair (Encodable.encode b) (2*(2*Nat.pair w (Nat.pair (Encodable.encode a) (Nat.pair i j))+1)+1))

def encodeGame (G : BCSGame) : GameCode := by
  classical
  exact ((enumFin G.contexts).entries.map (fun c =>
      (c.val,(enumFixed (Fin G.numVars → Bool)).entries.map Encodable.encode)),
    (enumFin G.numVars).entries.map Fin.val,
    (enumFin G.contexts).entries.flatMap fun c => (enumFin G.numVars).entries.map fun w =>
      (c.val,w.val,G.probability c w,(G.allowed c).toList.map fun a => (Encodable.encode a,a w)))

def testPoly (d : ℕ) (t : Test) : CPoly :=
  cmul (cconst t.2.2.1) (csum (t.2.2.2.map fun a =>
    rTotal₂ d fun i j => rTotal₂ d fun k l =>
      cmul (sR false i j k l) (cmul (sA false t.1 a.1 k i) (sB false t.2.1 a.2 l j))))

def constraints (g : GameCode) (eps : ℚ) (d : ℕ) : Sentence :=
  rAll₂ d (fun i j => rAll₂ d fun k l => ceq (sR false i j k l)
    (rTotal₂ d fun p q => cmul (cstar (sR true p q i j)) (sR true p q k l))) ++
  ceq (rTotal₂ d fun i j => sR false i j i j) cone ++
  g.1.flatMap (fun ca =>
    ca.2.flatMap (fun a => rEq d (sA false ca.1 a) (rGram d (sA true ca.1 a))) ++
    rEq d (fun i j => csum (ca.2.map fun a => sA false ca.1 a i j)) rIdentity) ++
  g.2.1.flatMap (fun w =>
    all (enumFixed Bool) (fun b => rEq d (sB false w b) (rGram d (sB true w b))) ++
    rEq d (fun i j => total (enumFixed Bool) fun b => sB false w b i j) rIdentity) ++
  [(false,sub (constant eps) (sub (constant 1) (csum (g.2.2.map (testPoly d))).1))]

def sentence (g : GameCode) (eps : ℚ) (d : ℕ) : Sentence :=
  if d=0 then [(false,constant (-1))] else constraints g eps d

theorem rawR_eq (G : BCSGame) (b : Bool) (i j k l : ℕ) : rR G b i j k l = sR b i j k l := rfl
theorem rawA_eq (G : BCSGame) (b : Bool) (c : Fin G.contexts)
    (a : Fin G.numVars → Bool) (i j : ℕ) : rA G b c a i j = sA b c (Encodable.encode a) i j := rfl
theorem rawB_eq (G : BCSGame) (b : Bool) (w : Fin G.numVars)
    (a : Bool) (i j : ℕ) : rB G b w a i j = sB b w a i j := rfl

set_option backward.isDefEq.respectTransparency false in
theorem encodeGame_correct (G : BCSGame) (eps : ℚ) (d : ℕ) :
    sentence (encodeGame G) eps d = FeasibilitySentence.sentence G eps d := by
  classical
  rw [sentence_eq_raw]
  unfold sentence rSentence
  congr 1
  simp only [constraints,rConstraints,encodeGame,testPoly,rWinning,rRGram,rGram,rEq,
    rawR_eq,rawA_eq,rawB_eq,all,total,List.flatMap_map,List.map_map,
    List.map_flatMap,csum_flatMap,Function.comp_def]

set_option maxHeartbeats 500000 in
/-- Uniform in the encoded finite game, the rational precision, and dimension. -/
theorem sentence_primrec : Primrec (fun p : GameCode × ℚ × ℕ => sentence p.1 p.2.1 p.2.2) := by
  classical
  have hc : Primrec (fun p : GameCode × ℚ × ℕ => constraints p.1 p.2.1 p.2.2) := by
    unfold constraints rAll₂ rTotal₂ rEq rGram testPoly sR sA sB
    code_primrec
  exact ite (Primrec.eq.comp (snd.comp snd) (const 0)) (const _) hc

theorem truth_iff_feasible (G : BCSGame) (eps : ℚ) (d : ℕ) :
    Truth (sentence (encodeGame G) eps d) ↔ Feasible G eps d := by
  rw [encodeGame_correct]
  exact FeasibilitySentence.truth_iff_feasible G eps d

end
end E2.FeasibilityUniform
