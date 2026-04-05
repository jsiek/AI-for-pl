universe u v

namespace Extrinsic

abbrev SigmaOmega (A : Sort u) (B : A → Sort v) := PSigma B
abbrev ExistsOmega {A : Sort u} (B : A → Sort v) := SigmaOmega A B

abbrev ProdOmega (A : Sort u) (B : Sort v) :=
  PProd A B

infixr:35 " ×ω " => ProdOmega

def proj1Omega {A : Sort u} {B : A → Sort v} (p : SigmaOmega A B) : A := p.1
def proj2Omega {A : Sort u} {B : A → Sort v} (p : SigmaOmega A B) : B p.1 := p.2

end Extrinsic
