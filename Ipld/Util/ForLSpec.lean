import LSpec

variable {α β : Type} [BEq β] 

-- new specification that we can add
@[reducible] def exceptDepEquals [BEq (Except σ β)] (f : α → Except σ β) : SpecOn f:=
⟨α × β, fun (a, b) => f a == Except.ok b ⟩

section test

structure weirdNat where
  n : Nat

def foo (n : weirdNat) : Except String weirdNat := match n.1 with
  | 0 => Except.error "Oh no got zero!"
  | m => Except.ok ⟨m⟩

def bar (n : weirdNat) : weirdNat := ⟨1 + n.1⟩ 

instance : BEq (Except String weirdNat) where
  beq
  | Except.ok x, Except.ok y => x.1 == y.1
  | Except.error x, Except.error y => x == y
  | _, _ => false

mkspec fooBarSpec : foo ∘ bar := exceptDepEquals (foo ∘ bar)

#reduce fooBarSpec.testParam
#check ((⟨2⟩,⟨3⟩) : fooBarSpec.testParam)
#spec Test fooBarSpec with (⟨2⟩,⟨3⟩)

end test
