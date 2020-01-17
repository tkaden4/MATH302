import Prelude.Nat

-- Not in axiom list, but covered in class
postulate powerDistributesRightMult : (a : Nat) -> (b : Nat) -> (k : Nat) -> power (a * b) k = (power a k) * (power b k)

-- a | b
data Divides : (a: Nat) -> (b: Nat) -> Type where
  MkDivides : DPair Nat (\n => b = n * a) -> Divides a b


-- a = b & x = y -> a + x = b + y
additionEquality : {a: Nat} -> {b: Nat} -> a = n -> b = m -> a + b = n + m
additionEquality pa pb = 
  rewrite pa in 
  rewrite pb in 
  Refl

-- a | b & a | c -> a | (b + c)
theorem1_1 : {a: Nat} -> {b: Nat} -> {c: Nat} -> Divides a b -> Divides a c -> Divides a (b + c)
theorem1_1 {a} {b} {c} (MkDivides (bFactor ** bProof)) (MkDivides (cFactor ** cProof)) =
  let result = additionEquality bProof cProof in
  let proofOfDist = multDistributesOverPlusLeft bFactor cFactor a in
  MkDivides ((bFactor + cFactor) ** (rewrite proofOfDist in result))

-- a | b & b | c -> a | c
theorem1_2 : {a : Nat} -> {b : Nat} -> {c : Nat} -> Divides a b -> Divides b c -> Divides a c
theorem1_2 {a} {b} {c} (MkDivides (bFactor ** bProof)) (MkDivides (cFactor ** cProof)) =
  rewrite cProof in
  rewrite bProof in
  MkDivides((cFactor * bFactor) ** multAssociative cFactor bFactor a)

-- a | b -> a^k | b^k
theorem1_4 : {a : Nat} -> {b : Nat} -> {k : Nat} -> Divides a b -> Divides (power a k) (power b k) 
theorem1_4 {a} {k} (MkDivides (bFactor ** bProof)) =
  rewrite bProof in 
  MkDivides((power bFactor k) ** powerDistributesRightMult bFactor a k)