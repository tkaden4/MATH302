import Prelude.Nat

-- Not in axiom list, but covered in class
-- (ab)^k = a^k * b^k
postulate powerDistributesRightMult : (a : Nat) -> (b : Nat) -> (k : Nat) -> power (a * b) k = (power a k) * (power b k)

-- a | b
Divides : (a : Nat) -> (b : Nat) -> Type
Divides a b = DPair Nat (\n => b = n * a)

-- a = b & x = y -> a + x = b + y
additionEquality : {a : Nat} -> {b : Nat} -> a = n -> b = m -> a + b = n + m
additionEquality pa pb = 
  rewrite pa in 
  rewrite pb in 
  Refl

-- a | b & a | c -> a | (b + c)
theorem1_1 : {a : Nat} -> {b : Nat} -> {c : Nat} -> Divides a b -> Divides a c -> Divides a (b + c)
theorem1_1 {a} {b} {c} (bFactor ** bProof) (cFactor ** cProof) =
  let result = additionEquality bProof cProof in
  let proofOfDist = multDistributesOverPlusLeft bFactor cFactor a in
  ((bFactor + cFactor) ** (rewrite proofOfDist in result))

-- a | b & b | c -> a | c
theorem1_2 : {a : Nat} -> {b : Nat} -> {c : Nat} -> Divides a b -> Divides b c -> Divides a c
theorem1_2 {a} {b} {c} (bFactor ** bProof) (cFactor ** cProof) =
  rewrite cProof in
  rewrite bProof in
  ((cFactor * bFactor) ** multAssociative cFactor bFactor a)

-- a | b -> a^k | b^k
theorem1_4 : {a : Nat} -> {b : Nat} -> {k : Nat} -> Divides a b -> Divides (power a k) (power b k) 
theorem1_4 {a} {k} (bFactor ** bProof) =
  rewrite bProof in 
  ((power bFactor k) ** powerDistributesRightMult bFactor a k)