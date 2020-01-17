import Prelude.Nat

data Divides : (a: Nat) -> (b: Nat) -> Type where
  MkDivides : DPair Nat (\n => b = n * a) -> Divides a b



additionEquality : {a: Nat} -> {b: Nat} -> a = n -> b = m -> a + b = n + m
additionEquality pa pb = 
  rewrite pa in 
  rewrite pb in 
  Refl

-- Divisability over plus
theorem1_1 : {a: Nat} -> {b: Nat} -> {c: Nat} -> Divides a b -> Divides a c -> Divides a (b + c)
theorem1_1 {a} {b} {c} (MkDivides (bFactor ** bProof)) (MkDivides (cFactor ** cProof)) =
  let result = additionEquality bProof cProof in
  let proofOfDist = multDistributesOverPlusLeft bFactor cFactor a in
  MkDivides ((bFactor + cFactor) ** (rewrite proofOfDist in result))

-- Divisability is transitive
theorem1_2 : {a : Nat} -> {b : Nat} -> {c : Nat} -> Divides a b -> Divides b c -> Divides a c
theorem1_2 {a} {b} {c} (MkDivides (bFactor ** bProof)) (MkDivides (cFactor ** cProof)) =
  rewrite cProof in
  rewrite bProof in
  MkDivides((cFactor * bFactor) ** multAssociative cFactor bFactor a)