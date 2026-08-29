/-
Copyright (c) 2021 Jakob Scholbach. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob Scholbach
-/
module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.CharP.Lemmas

/-!
### The Frobenius endomorphism

## Tags

Frobenius endomorphism

## Implementation notes

The definitions of `frobenius` and `iterateFrobenius` ring homomorphisms are in
`Mathlib/Algebra/CharP/Lemmas.lean` as they are needed for some results that in turn are used in
files forbidding to import algebra-related definitions (see `Mathlib/Algebra/CharP/Two.lean`).
-/

@[expose] public section

section CommSemiring

variable {R : Type*} [CommSemiring R] {S : Type*} [CommSemiring S]
variable (f : R ->* S) (g : R ->+* S) (p m n : Nat) [ExpChar R p] [ExpChar S p] (x y : R)

/--
lemma `frobenius_def` / 引理 `frobenius_def`

English:
lemma frobenius_def
  statement: frobenius R p x = x ^ p
  proof: rfl

中文:
引理 frobenius_def
  结论: frobenius R p x = x ^ p
  证明: rfl
-/
lemma frobenius_def : frobenius R p x = x ^ p := rfl

/--
lemma `iterateFrobenius_def` / 引理 `iterateFrobenius_def`

English:
lemma iterateFrobenius_def
  statement: iterateFrobenius R p n x = x ^ p ^ n
  proof: rfl

中文:
引理 iterateFrobenius_def
  结论: iterateFrobenius R p n x = x ^ p ^ n
  证明: rfl
-/
lemma iterateFrobenius_def : iterateFrobenius R p n x = x ^ p ^ n := rfl

/--
lemma `iterate_frobenius` / 引理 `iterate_frobenius`

English:
lemma iterate_frobenius
  statement: (frobenius R p)^[n] x = x ^ p ^ n
  proof: congr_fun (pow_iterate p n) x

中文:
引理 iterate_frobenius
  结论: (frobenius R p)^[n] x = x ^ p ^ n
  证明: congr_fun (pow_iterate p n) x

Depends on / 依赖: congr_fun, pow_iterate
-/
lemma iterate_frobenius : (frobenius R p)^[n] x = x ^ p ^ n := congr_fun (pow_iterate p n) x

variable (R)

/--
lemma `iterateFrobenius_eq_pow` / 引理 `iterateFrobenius_eq_pow`

English:
lemma iterateFrobenius_eq_pow
  statement: iterateFrobenius R p n = frobenius R p ^ n
  proof: by
  ext; simp [iterateFrobenius_def, iterate_frobenius]

中文:
引理 iterateFrobenius_eq_pow
  结论: iterateFrobenius R p n = frobenius R p ^ n
  证明: by
  ext; simp [iterateFrobenius_def, iterate_frobenius]

Depends on / 依赖: iterateFrobenius_def, iterate_frobenius
-/
lemma iterateFrobenius_eq_pow : iterateFrobenius R p n = frobenius R p ^ n := by
  ext; simp [iterateFrobenius_def, iterate_frobenius]

/--
lemma `coe_iterateFrobenius` / 引理 `coe_iterateFrobenius`

English:
lemma coe_iterateFrobenius
  statement: iterateFrobenius R p n = (frobenius R p)^[n]
  proof: (pow_iterate p n).symm

中文:
引理 coe_iterateFrobenius
  结论: iterateFrobenius R p n = (frobenius R p)^[n]
  证明: (pow_iterate p n).symm

Depends on / 依赖: pow_iterate
-/
lemma coe_iterateFrobenius : iterateFrobenius R p n = (frobenius R p)^[n] :=
  (pow_iterate p n).symm

/--
lemma `iterateFrobenius_one_apply` / 引理 `iterateFrobenius_one_apply`

English:
lemma iterateFrobenius_one_apply
  statement: iterateFrobenius R p 1 x = x ^ p
  proof: by
  rw [iterateFrobenius_def]; rw [pow_one]

@[simp]

中文:
引理 iterateFrobenius_one_apply
  结论: iterateFrobenius R p 1 x = x ^ p
  证明: by
  rw [iterateFrobenius_def]; rw [pow_one]

@[simp]

Depends on / 依赖: iterateFrobenius_def, pow_one
-/
lemma iterateFrobenius_one_apply : iterateFrobenius R p 1 x = x ^ p := by
  rw [iterateFrobenius_def]; rw [pow_one]

@[simp]
/--
lemma `iterateFrobenius_one` / 引理 `iterateFrobenius_one`

English:
lemma iterateFrobenius_one
  statement: iterateFrobenius R p 1 = frobenius R p
  proof: RingHom.ext (iterateFrobenius_one_apply R p)

中文:
引理 iterateFrobenius_one
  结论: iterateFrobenius R p 1 = frobenius R p
  证明: RingHom.ext (iterateFrobenius_one_apply R p)

Depends on / 依赖: RingHom, RingHom.ext, iterateFrobenius_one_apply
-/
lemma iterateFrobenius_one : iterateFrobenius R p 1 = frobenius R p :=
  RingHom.ext (iterateFrobenius_one_apply R p)

/--
lemma `iterateFrobenius_zero_apply` / 引理 `iterateFrobenius_zero_apply`

English:
lemma iterateFrobenius_zero_apply
  statement: iterateFrobenius R p 0 x = x
  proof: by
  rw [iterateFrobenius_def]; rw [pow_zero]; rw [pow_one]

@[simp]

中文:
引理 iterateFrobenius_zero_apply
  结论: iterateFrobenius R p 0 x = x
  证明: by
  rw [iterateFrobenius_def]; rw [pow_zero]; rw [pow_one]

@[simp]

Depends on / 依赖: iterateFrobenius_def, pow_one, pow_zero
-/
lemma iterateFrobenius_zero_apply : iterateFrobenius R p 0 x = x := by
  rw [iterateFrobenius_def]; rw [pow_zero]; rw [pow_one]

@[simp]
/--
lemma `iterateFrobenius_zero` / 引理 `iterateFrobenius_zero`

English:
lemma iterateFrobenius_zero
  statement: iterateFrobenius R p 0 = RingHom.id R
  proof: RingHom.ext (iterateFrobenius_zero_apply R p)

中文:
引理 iterateFrobenius_zero
  结论: iterateFrobenius R p 0 = 环态射.id R
  证明: RingHom.ext (iterateFrobenius_zero_apply R p)

Depends on / 依赖: RingHom, RingHom.ext, iterateFrobenius_zero_apply
-/
lemma iterateFrobenius_zero : iterateFrobenius R p 0 = RingHom.id R :=
  RingHom.ext (iterateFrobenius_zero_apply R p)

/--
lemma `iterateFrobenius_add_apply` / 引理 `iterateFrobenius_add_apply`

English:
lemma iterateFrobenius_add_apply
  proof: by
  simp_rw [iterateFrobenius_def, add_comm m n, pow_add, pow_mul]

中文:
引理 iterateFrobenius_add_apply
  证明: by
  simp_rw [iterateFrobenius_def, add_comm m n, pow_add, pow_mul]

Depends on / 依赖: add_comm, iterateFrobenius_def, pow_add, pow_mul, simp_rw
-/
lemma iterateFrobenius_add_apply :
    iterateFrobenius R p (m + n) x = iterateFrobenius R p m (iterateFrobenius R p n x) := by
  simp_rw [iterateFrobenius_def, add_comm m n, pow_add, pow_mul]

/--
lemma `iterateFrobenius_add` / 引理 `iterateFrobenius_add`

English:
lemma iterateFrobenius_add
  proof: RingHom.ext (iterateFrobenius_add_apply R p m n)

中文:
引理 iterateFrobenius_add
  证明: RingHom.ext (iterateFrobenius_add_apply R p m n)

Depends on / 依赖: RingHom, RingHom.ext, iterateFrobenius_add_apply
-/
lemma iterateFrobenius_add :
    iterateFrobenius R p (m + n) = (iterateFrobenius R p m).comp (iterateFrobenius R p n) :=
  RingHom.ext (iterateFrobenius_add_apply R p m n)

/--
lemma `iterateFrobenius_mul_apply` / 引理 `iterateFrobenius_mul_apply`

English:
lemma iterateFrobenius_mul_apply
  proof: by
  simp_rw [coe_iterateFrobenius, Function.iterate_mul]

中文:
引理 iterateFrobenius_mul_apply
  证明: by
  simp_rw [coe_iterateFrobenius, Function.iterate_mul]

Depends on / 依赖: Function, Function.iterate_mul, coe_iterateFrobenius, iterate_mul, simp_rw
-/
lemma iterateFrobenius_mul_apply :
    iterateFrobenius R p (m * n) x = (iterateFrobenius R p m)^[n] x := by
  simp_rw [coe_iterateFrobenius, Function.iterate_mul]

/--
lemma `coe_iterateFrobenius_mul` / 引理 `coe_iterateFrobenius_mul`

English:
lemma coe_iterateFrobenius_mul
  statement: iterateFrobenius R p (m * n) = (iterateFrobenius R p m)^[n]
  proof: funext (iterateFrobenius_mul_apply R p m n)

中文:
引理 coe_iterateFrobenius_mul
  结论: iterateFrobenius R p (m * n) = (iterateFrobenius R p m)^[n]
  证明: funext (iterateFrobenius_mul_apply R p m n)

Depends on / 依赖: iterateFrobenius_mul_apply
-/
lemma coe_iterateFrobenius_mul : iterateFrobenius R p (m * n) = (iterateFrobenius R p m)^[n] :=
  funext (iterateFrobenius_mul_apply R p m n)

variable {R}

/--
lemma `MonoidHom.map_frobenius` / 引理 `MonoidHom.map_frobenius`

English:
lemma MonoidHom.map_frobenius
  statement: f (frobenius R p x) = frobenius S p (f x)
  proof: map_pow f x p

中文:
引理 幺半群态射.map_frobenius
  结论: f (frobenius R p x) = frobenius S p (f x)
  证明: map_pow f x p

Depends on / 依赖: map_pow
-/
lemma MonoidHom.map_frobenius : f (frobenius R p x) = frobenius S p (f x) := map_pow f x p
/--
lemma `RingHom.map_frobenius` / 引理 `RingHom.map_frobenius`

English:
lemma RingHom.map_frobenius
  statement: g (frobenius R p x) = frobenius S p (g x)
  proof: map_pow g x p

中文:
引理 环态射.map_frobenius
  结论: g (frobenius R p x) = frobenius S p (g x)
  证明: map_pow g x p

Depends on / 依赖: map_pow
-/
lemma RingHom.map_frobenius : g (frobenius R p x) = frobenius S p (g x) := map_pow g x p

/--
lemma `MonoidHom.map_iterate_frobenius` / 引理 `MonoidHom.map_iterate_frobenius`

English:
lemma MonoidHom.map_iterate_frobenius
  given: (n : Nat)
  proof: Function.Semiconj.iterate_right (f.map_frobenius p) n x

中文:
引理 幺半群态射.map_iterate_frobenius
  条件: (n : 自然数)
  证明: Function.Semiconj.iterate_right (f.map_frobenius p) n x

Depends on / 依赖: Function, Function.Semiconj.iterate_right, Semiconj, f.map_frobenius, iterate_right, map_frobenius
-/
lemma MonoidHom.map_iterate_frobenius (n : Nat) :
    f ((frobenius R p)^[n] x) = (frobenius S p)^[n] (f x) :=
  Function.Semiconj.iterate_right (f.map_frobenius p) n x

/--
lemma `MonoidHom.map_iterateFrobenius` / 引理 `MonoidHom.map_iterateFrobenius`

English:
lemma MonoidHom.map_iterateFrobenius
  given: (n : Nat)
  proof: by
  simp [iterateFrobenius_def]

中文:
引理 幺半群态射.map_iterateFrobenius
  条件: (n : 自然数)
  证明: by
  simp [iterateFrobenius_def]

Depends on / 依赖: iterateFrobenius_def
-/
lemma MonoidHom.map_iterateFrobenius (n : Nat) :
    f (iterateFrobenius R p n x) = iterateFrobenius S p n (f x) := by
  simp [iterateFrobenius_def]

/--
lemma `RingHom.map_iterate_frobenius` / 引理 `RingHom.map_iterate_frobenius`

English:
lemma RingHom.map_iterate_frobenius
  given: (n : Nat)
  proof: g.toMonoidHom.map_iterate_frobenius p x n

中文:
引理 环态射.map_iterate_frobenius
  条件: (n : 自然数)
  证明: g.toMonoidHom.map_iterate_frobenius p x n

Depends on / 依赖: g.toMonoidHom.map_iterate_frobenius, map_iterate_frobenius, toMonoidHom
-/
lemma RingHom.map_iterate_frobenius (n : Nat) :
    g ((frobenius R p)^[n] x) = (frobenius S p)^[n] (g x) :=
  g.toMonoidHom.map_iterate_frobenius p x n

/--
lemma `RingHom.map_iterateFrobenius` / 引理 `RingHom.map_iterateFrobenius`

English:
lemma RingHom.map_iterateFrobenius
  given: (n : Nat)
  proof: g.toMonoidHom.map_iterateFrobenius p x n

中文:
引理 环态射.map_iterateFrobenius
  条件: (n : 自然数)
  证明: g.toMonoidHom.map_iterateFrobenius p x n

Depends on / 依赖: g.toMonoidHom.map_iterateFrobenius, map_iterateFrobenius, toMonoidHom
-/
lemma RingHom.map_iterateFrobenius (n : Nat) :
    g (iterateFrobenius R p n x) = iterateFrobenius S p n (g x) :=
  g.toMonoidHom.map_iterateFrobenius p x n

/--
lemma `MonoidHom.iterate_map_frobenius` / 引理 `MonoidHom.iterate_map_frobenius`

English:
lemma MonoidHom.iterate_map_frobenius
  given: (f : R ->* R) (p : Nat) [ExpChar R p] (n : Nat)
  proof: iterate_map_pow f _ _ _

中文:
引理 幺半群态射.iterate_map_frobenius
  条件: (f : R ->* R) (p : 自然数) [ExpChar R p] (n : 自然数)
  证明: iterate_map_pow f _ _ _

Depends on / 依赖: Quotient, Quotient.mk, iterate_map_pow
-/
lemma MonoidHom.iterate_map_frobenius (f : R ->* R) (p : Nat) [ExpChar R p] (n : Nat) :
    f^[n] (frobenius R p x) = frobenius R p (f^[n] x) :=
  iterate_map_pow f _ _ _

/--
lemma `RingHom.iterate_map_frobenius` / 引理 `RingHom.iterate_map_frobenius`

English:
lemma RingHom.iterate_map_frobenius
  given: (f : R ->+* R) (p : Nat) [ExpChar R p] (n : Nat)
  proof: iterate_map_pow f _ _ _

中文:
引理 环态射.iterate_map_frobenius
  条件: (f : R ->+* R) (p : 自然数) [ExpChar R p] (n : 自然数)
  证明: iterate_map_pow f _ _ _

Depends on / 依赖: Quotient, Quotient.map, iterate_map_pow
-/
lemma RingHom.iterate_map_frobenius (f : R ->+* R) (p : Nat) [ExpChar R p] (n : Nat) :
    f^[n] (frobenius R p x) = frobenius R p (f^[n] x) := iterate_map_pow f _ _ _

/--
lemma `RingHom.frobenius_comm` / 引理 `RingHom.frobenius_comm`

English:
lemma RingHom.frobenius_comm
  statement: g.comp (frobenius R p) = (frobenius S p).comp g
  proof: ext map_frobenius g p

中文:
引理 环态射.frobenius_comm
  结论: g.comp (frobenius R p) = (frobenius S p).comp g
  证明: ext map_frobenius g p

Depends on / 依赖: Quotient, Quotient.map, Relation, Relation.neg_1, map_frobenius, neg_1
-/
lemma RingHom.frobenius_comm : g.comp (frobenius R p) = (frobenius S p).comp g :=
ext map_frobenius g p

/--
lemma `RingHom.iterateFrobenius_comm` / 引理 `RingHom.iterateFrobenius_comm`

English:
lemma RingHom.iterateFrobenius_comm
  given: (n : Nat)
  proof: ext fun x => map_iterateFrobenius g p x n

中文:
引理 环态射.iterateFrobenius_comm
  条件: (n : 自然数)
  证明: ext fun x => map_iterateFrobenius g p x n

Depends on / 依赖: Quotient, Quotient.map, Relation, Relation.neg_1, map_iterateFrobenius, neg_1
-/
lemma RingHom.iterateFrobenius_comm (n : Nat) :
    g.comp (iterateFrobenius R p n) = (iterateFrobenius S p n).comp g :=
  ext fun x => map_iterateFrobenius g p x n

variable (R S)

/-- The Frobenius map of an algebra as a Frobenius-semilinear map. -/
nonrec def LinearMap.frobenius [Algebra R S] : S ->ₛₗ[frobenius R p] S where
  __ := frobenius S p
  map_smul' r s := show frobenius S p _ = _ by
    simp_rw [Algebra.smul_def, map_mul, ← (algebraMap R S).map_frobenius]; rfl

/-- The iterated Frobenius map of an algebra as an iterated-Frobenius-semilinear map. -/
nonrec def LinearMap.iterateFrobenius [Algebra R S] : S ->ₛₗ[iterateFrobenius R p n] S where
  __ := iterateFrobenius S p n
  map_smul' f s := show iterateFrobenius S p n _ = _ by
    simp_rw [iterateFrobenius_def, Algebra.smul_def, mul_pow, ← map_pow]; rfl

/--
theorem `LinearMap.frobenius_def` / 定理 `LinearMap.frobenius_def`

English:
theorem LinearMap.frobenius_def
  given: [Algebra R S] (x : S)
  statement: frobenius R S p x = x ^ p
  proof: rfl

中文:
定理 线性映射.frobenius_def
  条件: [代数 R S] (x : S)
  结论: frobenius R S p x = x ^ p
  证明: rfl
-/
theorem LinearMap.frobenius_def [Algebra R S] (x : S) : frobenius R S p x = x ^ p := rfl

/--
theorem `LinearMap.iterateFrobenius_def` / 定理 `LinearMap.iterateFrobenius_def`

English:
theorem LinearMap.iterateFrobenius_def
  given: [Algebra R S] (n : Nat) (x : S)
  proof: rfl

中文:
定理 线性映射.iterateFrobenius_def
  条件: [代数 R S] (n : 自然数) (x : S)
  证明: rfl

Depends on / 依赖: AddGroup, ColimitType, ColimitType.AddGroup, Quotient, Quotient.mk
-/
theorem LinearMap.iterateFrobenius_def [Algebra R S] (n : Nat) (x : S) :
    iterateFrobenius R S p n x = x ^ p ^ n := rfl

end CommSemiring

section CommRing

variable {R : Type*} [CommRing R] (p : Nat) [ExpChar R p] (x y : R)

end CommRing
