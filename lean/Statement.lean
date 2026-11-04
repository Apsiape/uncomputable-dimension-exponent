import E2.Computability
import E2.RealArithmetic

namespace E2

def MainStatement : Prop :=
  ∃ G : BCSGame,
    quantumValue G = 1 ∧
    NoPerfectStrategy G ∧
    DimensionExponent G betaK ∧
    ExponentHasHaltingDegree ∧
    ¬ CertifiedRate (dyadicSlope G) betaK


end E2
