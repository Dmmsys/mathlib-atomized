/-
Copyright (c) 2024 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Algebra.AddConstMap.Basic

/-!
# Equivalences conjugating `(· + a)` to `(· + b)`

In this file we define `AddConstEquiv G H a b` (notation: `G ≃+c[a, b] H`)
to be the type of equivalences such that `∀ x, f (x + a) = f x + b`.

We also define the corresponding typeclass and prove some basic properties.
-/

@[expose] public section

assert_not_exists Finset

open Function
open scoped AddConstMap

/--
Definition of `AddConstEquiv` / `AddConstEquiv` 的定义

English:
structure AddConstEquiv
  parameters: (G H : Type*) [Add G] [Add H] (a : G) (b : H)
  extends: G ≃ H, G ->+c[a, b] H
  (no additional axioms)

中文:
结构 加法余nst等价
  参数: (G H : 类型) [加法 G] [加法 H] (a : G) (b : H)
  继承: G ≃ H, G ->+c[a, b] H
  (无附加公理)
-/
structure AddConstEquiv (G H : Type*) [Add G] [Add H] (a : G) (b : H)
  extends G ≃ H, G ->+c[a, b] H

/-- Interpret an `AddConstEquiv` as an `Equiv`. -/
add_decl_doc AddConstEquiv.toEquiv

/-- Interpret an `AddConstEquiv` as an `AddConstMap`. -/
add_decl_doc AddConstEquiv.toAddConstMap

@[inherit_doc]
scoped[AddConstMap] notation:25 G " ≃+c[" a ", " b "] " H => AddConstEquiv G H a b

namespace AddConstEquiv

variable {G H K : Type*} [Add G] [Add H] [Add K] {a : G} {b : H} {c : K}

/--
lemma `toEquiv_injective` / 引理 `toEquiv_injective`

English:
lemma toEquiv_injective
  statement: Injective (toEquiv : (G ≃+c[a, b] H) -> G ≃ H)

中文:
引理 toEquiv_injective
  结论: 单射 (toEquiv : (G ≃+c[a, b] H) -> G ≃ H)
-/
lemma toEquiv_injective : Injective (toEquiv : (G ≃+c[a, b] H) -> G ≃ H)
  | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl

instance {G H : Type*} [Add G] [Add H] {a : G} {b : H} :
    EquivLike (G ≃+c[a, b] H) G H where
  coe f := f.toEquiv
  inv f := f.toEquiv.symm
  left_inv f := f.left_inv
  right_inv f := f.right_inv
coe_injective' _ _ h _ := toEquiv_injective DFunLike.ext' h

instance {G H : Type*} [Add G] [Add H] {a : G} {b : H} :
    AddConstMapClass (G ≃+c[a, b] H) G H a b where
  map_add_const f x := f.map_add_const' x

/--
lemma `ext` / 引理 `ext`

English:
lemma ext
  given: {e₁ e₂ : G ≃+c[a, b] H} (h : forall x, e₁ x = e₂ x)
  statement: e₁ = e₂
  proof: DFunLike.ext _ _ h

@[simp]

中文:
引理 ext
  条件: {e₁ e₂ : G ≃+c[a, b] H} (h : 对任意 x, e₁ x = e₂ x)
  结论: e₁ = e₂
  证明: DFunLike.ext _ _ h

@[simp]
-/
@[ext] lemma ext {e₁ e₂ : G ≃+c[a, b] H} (h : forall x, e₁ x = e₂ x) : e₁ = e₂ := DFunLike.ext _ _ h

@[simp]
/--
lemma `toEquiv_inj` / 引理 `toEquiv_inj`

English:
lemma toEquiv_inj
  given: {e₁ e₂ : G ≃+c[a, b] H}
  statement: e₁.toEquiv = e₂.toEquiv ↔ e₁ = e₂
  proof: toEquiv_injective.eq_iff

中文:
引理 toEquiv_inj
  条件: {e₁ e₂ : G ≃+c[a, b] H}
  结论: e₁.toEquiv = e₂.toEquiv ↔ e₁ = e₂
  证明: toEquiv_injective.eq_iff

Depends on / 依赖: eq_iff, toEquiv_injective, toEquiv_injective.eq_iff
-/
lemma toEquiv_inj {e₁ e₂ : G ≃+c[a, b] H} : e₁.toEquiv = e₂.toEquiv ↔ e₁ = e₂ :=
  toEquiv_injective.eq_iff

/--
lemma `coe_toEquiv` / 引理 `coe_toEquiv`

English:
lemma coe_toEquiv
  given: (e : G ≃+c[a, b] H)
  statement: ⇑e.toEquiv = e
  proof: rfl

中文:
引理 coe_toEquiv
  条件: (e : G ≃+c[a, b] H)
  结论: ⇑e.toEquiv = e
  证明: rfl
-/
@[simp] lemma coe_toEquiv (e : G ≃+c[a, b] H) : ⇑e.toEquiv = e := rfl

/--
Definition of `symm` / `symm` 的定义

English:
definition symm
  signature: (e : G ≃+c[a, b] H)
  body: e.toEquiv.symm
  map_add_const' := (AddConstMapClass.semiconj e).inverse_left e.left_inv e.right_inv

中文:
定义 symm
  签名: (e : G ≃+c[a, b] H)
  定义体: e.toEquiv.symm
  map_add_const' := (AddConstMapClass.semiconj e).inverse_left e.left_inv e.right_inv

Depends on / 依赖: e.toEquiv.symm, toEquiv
-/
def symm (e : G ≃+c[a, b] H) : H ≃+c[b, a] G where
  toEquiv := e.toEquiv.symm
  map_add_const' := (AddConstMapClass.semiconj e).inverse_left e.left_inv e.right_inv

/--
Definition of `Simps.symm_apply` / `Simps.symm_apply` 的定义

English:
definition Simps.symm_apply
  signature: (e : G ≃+c[a, b] H)
  body: e.symm

initialize_simps_projections AddConstEquiv (toFun -> apply, invFun -> symm_apply)

中文:
定义 Simps.symm_apply
  签名: (e : G ≃+c[a, b] H)
  定义体: e.symm

initialize_simps_projections AddConstEquiv (toFun -> apply, invFun -> symm_apply)

Depends on / 依赖: e.symm
-/
def Simps.symm_apply (e : G ≃+c[a, b] H) : H -> G := e.symm

initialize_simps_projections AddConstEquiv (toFun -> apply, invFun -> symm_apply)

/--
lemma `symm_symm` / 引理 `symm_symm`

English:
lemma symm_symm
  given: (e : G ≃+c[a, b] H)
  statement: e.symm.symm = e
  proof: rfl

中文:
引理 symm_symm
  条件: (e : G ≃+c[a, b] H)
  结论: e.symm.symm = e
  证明: rfl
-/
@[simp] lemma symm_symm (e : G ≃+c[a, b] H) : e.symm.symm = e := rfl

/--
theorem `symm_apply_eq` / 定理 `symm_apply_eq`

English:
theorem symm_apply_eq
  given: (e : G ≃+c[a, b] H) {a b}
  proof: e.toEquiv.symm_apply_eq

中文:
定理 symm_apply_eq
  条件: (e : G ≃+c[a, b] H) {a b}
  证明: e.toEquiv.symm_apply_eq

Depends on / 依赖: e.toEquiv.symm_apply_eq, symm_apply_eq, toEquiv
-/
theorem symm_apply_eq (e : G ≃+c[a, b] H) {a b} :
    e.symm a = b ↔ a = e b :=
  e.toEquiv.symm_apply_eq

/--
theorem `eq_symm_apply` / 定理 `eq_symm_apply`

English:
theorem eq_symm_apply
  given: (e : G ≃+c[a, b] H) {a b}
  proof: e.toEquiv.eq_symm_apply

中文:
定理 eq_symm_apply
  条件: (e : G ≃+c[a, b] H) {a b}
  证明: e.toEquiv.eq_symm_apply

Depends on / 依赖: e.toEquiv.eq_symm_apply, eq_symm_apply, toEquiv
-/
theorem eq_symm_apply (e : G ≃+c[a, b] H) {a b} :
    b = e.symm a ↔ e b = a :=
  e.toEquiv.eq_symm_apply

/--
theorem `apply_symm_apply` / 定理 `apply_symm_apply`

English:
theorem apply_symm_apply
  given: (e : G ≃+c[a, b] H) (a)
  proof: e.toEquiv.apply_symm_apply _

中文:
定理 apply_symm_apply
  条件: (e : G ≃+c[a, b] H) (a)
  证明: e.toEquiv.apply_symm_apply _
-/
@[simp] theorem apply_symm_apply (e : G ≃+c[a, b] H) (a) :
    e (e.symm a) = a :=
  e.toEquiv.apply_symm_apply _

/--
theorem `symm_apply_apply` / 定理 `symm_apply_apply`

English:
theorem symm_apply_apply
  given: (e : G ≃+c[a, b] H) (a)
  proof: e.toEquiv.symm_apply_apply _

中文:
定理 symm_apply_apply
  条件: (e : G ≃+c[a, b] H) (a)
  证明: e.toEquiv.symm_apply_apply _
-/
@[simp] theorem symm_apply_apply (e : G ≃+c[a, b] H) (a) :
    e.symm (e a) = a :=
  e.toEquiv.symm_apply_apply _

/-- The identity map as an `AddConstEquiv`. -/
@[simps! toEquiv apply]
/--
Definition of `refl` / `refl` 的定义

English:
definition refl
  signature: (a : G)
  body: .refl G
  map_add_const' _ := rfl

中文:
定义 refl
  签名: (a : G)
  定义体: .refl G
  map_add_const' _ := rfl
-/
def refl (a : G) : G ≃+c[a, a] G where
  toEquiv := .refl G
  map_add_const' _ := rfl

/--
lemma `symm_refl` / 引理 `symm_refl`

English:
lemma symm_refl
  given: (a : G)
  statement: (refl a).symm = refl a
  proof: rfl

中文:
引理 symm_refl
  条件: (a : G)
  结论: (refl a).symm = refl a
  证明: rfl
-/
@[simp] lemma symm_refl (a : G) : (refl a).symm = refl a := rfl

/-- Composition of `AddConstEquiv`s, as an `AddConstEquiv`. -/
@[simps! +simpRhs toEquiv apply]
/--
Definition of `trans` / `trans` 的定义

English:
definition trans
  signature: (e₁ : G ≃+c[a, b] H) (e₂ : H ≃+c[b, c] K)
  body: e₁.toEquiv.trans e₂.toEquiv
  map_add_const' := (AddConstMapClass.semiconj e₁).trans (AddConstMapClass.semiconj e₂)

中文:
定义 trans
  签名: (e₁ : G ≃+c[a, b] H) (e₂ : H ≃+c[b, c] K)
  定义体: e₁.toEquiv.trans e₂.toEquiv
  map_add_const' := (AddConstMapClass.semiconj e₁).trans (AddConstMapClass.semiconj e₂)

Depends on / 依赖: toEquiv, toEquiv.trans
-/
def trans (e₁ : G ≃+c[a, b] H) (e₂ : H ≃+c[b, c] K) : G ≃+c[a, c] K where
  toEquiv := e₁.toEquiv.trans e₂.toEquiv
  map_add_const' := (AddConstMapClass.semiconj e₁).trans (AddConstMapClass.semiconj e₂)

/--
lemma `trans_refl` / 引理 `trans_refl`

English:
lemma trans_refl
  given: (e : G ≃+c[a, b] H)
  statement: e.trans (.refl b) = e
  proof: rfl

中文:
引理 trans_refl
  条件: (e : G ≃+c[a, b] H)
  结论: e.trans (.refl b) = e
  证明: rfl
-/
@[simp] lemma trans_refl (e : G ≃+c[a, b] H) : e.trans (.refl b) = e := rfl
/--
lemma `refl_trans` / 引理 `refl_trans`

English:
lemma refl_trans
  given: (e : G ≃+c[a, b] H)
  statement: (refl a).trans e = e
  proof: rfl

@[simp]

中文:
引理 refl_trans
  条件: (e : G ≃+c[a, b] H)
  结论: (refl a).trans e = e
  证明: rfl

@[simp]
-/
@[simp] lemma refl_trans (e : G ≃+c[a, b] H) : (refl a).trans e = e := rfl

@[simp]
/--
lemma `self_trans_symm` / 引理 `self_trans_symm`

English:
lemma self_trans_symm
  given: (e : G ≃+c[a, b] H)
  statement: e.trans e.symm = .refl a
  proof: toEquiv_injective e.toEquiv.self_trans_symm

@[simp]

中文:
引理 self_trans_symm
  条件: (e : G ≃+c[a, b] H)
  结论: e.trans e.symm = .refl a
  证明: toEquiv_injective e.toEquiv.self_trans_symm

@[simp]

Depends on / 依赖: e.toEquiv.self_trans_symm, self_trans_symm, toEquiv, toEquiv_injective
-/
lemma self_trans_symm (e : G ≃+c[a, b] H) : e.trans e.symm = .refl a :=
  toEquiv_injective e.toEquiv.self_trans_symm

@[simp]
/--
lemma `symm_trans_self` / 引理 `symm_trans_self`

English:
lemma symm_trans_self
  given: (e : G ≃+c[a, b] H)
  statement: e.symm.trans e = .refl b
  proof: toEquiv_injective e.toEquiv.symm_trans_self

@[simp]

中文:
引理 symm_trans_self
  条件: (e : G ≃+c[a, b] H)
  结论: e.symm.trans e = .refl b
  证明: toEquiv_injective e.toEquiv.symm_trans_self

@[simp]

Depends on / 依赖: e.toEquiv.symm_trans_self, symm_trans_self, toEquiv, toEquiv_injective
-/
lemma symm_trans_self (e : G ≃+c[a, b] H) : e.symm.trans e = .refl b :=
  toEquiv_injective e.toEquiv.symm_trans_self

@[simp]
/--
lemma `coe_symm_toEquiv` / 引理 `coe_symm_toEquiv`

English:
lemma coe_symm_toEquiv
  given: (e : G ≃+c[a, b] H)
  statement: ⇑e.toEquiv.symm = e.symm
  proof: rfl

@[simp]

中文:
引理 coe_symm_toEquiv
  条件: (e : G ≃+c[a, b] H)
  结论: ⇑e.toEquiv.symm = e.symm
  证明: rfl

@[simp]
-/
lemma coe_symm_toEquiv (e : G ≃+c[a, b] H) : ⇑e.toEquiv.symm = e.symm := rfl

@[simp]
/--
lemma `toEquiv_symm` / 引理 `toEquiv_symm`

English:
lemma toEquiv_symm
  given: (e : G ≃+c[a, b] H)
  statement: e.symm.toEquiv = e.toEquiv.symm
  proof: rfl

@[simp]

中文:
引理 toEquiv_symm
  条件: (e : G ≃+c[a, b] H)
  结论: e.symm.toEquiv = e.toEquiv.symm
  证明: rfl

@[simp]
-/
lemma toEquiv_symm (e : G ≃+c[a, b] H) : e.symm.toEquiv = e.toEquiv.symm := rfl

@[simp]
/--
lemma `toEquiv_trans` / 引理 `toEquiv_trans`

English:
lemma toEquiv_trans
  given: (e₁ : G ≃+c[a, b] H) (e₂ : H ≃+c[b, c] K)
  proof: rfl

中文:
引理 toEquiv_trans
  条件: (e₁ : G ≃+c[a, b] H) (e₂ : H ≃+c[b, c] K)
  证明: rfl
-/
lemma toEquiv_trans (e₁ : G ≃+c[a, b] H) (e₂ : H ≃+c[b, c] K) :
    (e₁.trans e₂).toEquiv = e₁.toEquiv.trans e₂.toEquiv := rfl

/--
Instance `instOne` / 实例 `instOne`

English:
instance instOne
  signature: : One (G ≃+c[a, a] G)
  body: ⟨.refl _⟩

中文:
实例 instOne
  签名: : 幺 (G ≃+c[a, a] G)
  定义体: ⟨.refl _⟩
-/
instance instOne : One (G ≃+c[a, a] G) := ⟨.refl _⟩
/--
Instance `instMul` / 实例 `instMul`

English:
instance instMul
  signature: : Mul (G ≃+c[a, a] G)
  body: ⟨fun f g => g.trans f⟩

中文:
实例 instMul
  签名: : 乘法 (G ≃+c[a, a] G)
  定义体: ⟨fun f g => g.trans f⟩

Depends on / 依赖: g.trans
-/
instance instMul : Mul (G ≃+c[a, a] G) := ⟨fun f g => g.trans f⟩
/--
Instance `instInv` / 实例 `instInv`

English:
instance instInv
  signature: : Inv (G ≃+c[a, a] G)
  body: ⟨.symm⟩

中文:
实例 instInv
  签名: : 取逆 (G ≃+c[a, a] G)
  定义体: ⟨.symm⟩
-/
instance instInv : Inv (G ≃+c[a, a] G) := ⟨.symm⟩
/--
Instance `instDiv` / 实例 `instDiv`

English:
instance instDiv
  signature: : Div (G ≃+c[a, a] G)
  body: ⟨fun f g => f * g⁻¹⟩

中文:
实例 instDiv
  签名: : 除法 (G ≃+c[a, a] G)
  定义体: ⟨fun f g => f * g⁻¹⟩
-/
instance instDiv : Div (G ≃+c[a, a] G) := ⟨fun f g => f * g⁻¹⟩

/--
Instance `instPowNat` / 实例 `instPowNat`

English:
instance instPowNat
  signature: : Pow (G ≃+c[a, a] G) Nat where
  body: ⟨e^n, (e.toAddConstMap^n).map_add_const'⟩

中文:
实例 instPow自然数
  签名: : 幂 (G ≃+c[a, a] G) 自然数 where
  定义体: ⟨e^n, (e.toAddConstMap^n).map_add_const'⟩

Depends on / 依赖: e.toAddConstMap, map_add_const, toAddConstMap
-/
instance instPowNat : Pow (G ≃+c[a, a] G) Nat where
  pow e n := ⟨e^n, (e.toAddConstMap^n).map_add_const'⟩

/--
Instance `instPowInt` / 实例 `instPowInt`

English:
instance instPowInt
  signature: : Pow (G ≃+c[a, a] G) Int where
  body: ⟨e^n,
    match n with
    | .ofNat n => (e^n).map_add_const'
    | .negSucc n => (e.symm^(n + 1)).map_add_const'⟩

中文:
实例 instPow整数
  签名: : 幂 (G ≃+c[a, a] G) 整数 where
  定义体: ⟨e^n,
    match n with
    | .ofNat n => (e^n).map_add_const'
    | .negSucc n => (e.symm^(n + 1)).map_add_const'⟩
-/
instance instPowInt : Pow (G ≃+c[a, a] G) Int where
  pow e n := ⟨e^n,
    match n with
    | .ofNat n => (e^n).map_add_const'
    | .negSucc n => (e.symm^(n + 1)).map_add_const'⟩

/--
Instance `instGroup` / 实例 `instGroup`

English:
instance instGroup
  signature: : Group (G ≃+c[a, a] G)
  body: toEquiv_injective.group _ rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    fun _ _ => rfl

中文:
实例 instGroup
  签名: : 群 (G ≃+c[a, a] G)
  定义体: toEquiv_injective.group _ rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    fun _ _ => rfl

Depends on / 依赖: toEquiv_injective, toEquiv_injective.group
-/
instance instGroup : Group (G ≃+c[a, a] G) :=
  toEquiv_injective.group _ rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    fun _ _ => rfl

/-- Projection from `G ≃+c[a, a] G` to permutations `G ≃ G`, as a monoid homomorphism. -/
@[simps! apply]
/--
Definition of `toPerm` / `toPerm` 的定义

English:
definition toPerm
  signature: : (G ≃+c[a, a] G) ->* Equiv.Perm G
  body: .mk' toEquiv fun _ _ => rfl

中文:
定义 toPerm
  签名: : (G ≃+c[a, a] G) ->* 等价.置换 G
  定义体: .mk' toEquiv fun _ _ => rfl

Depends on / 依赖: toEquiv
-/
def toPerm : (G ≃+c[a, a] G) ->* Equiv.Perm G :=
  .mk' toEquiv fun _ _ => rfl

/-- Projection from `G ≃+c[a, a] G` to `G →+c[a, a] G`, as a monoid homomorphism. -/
@[simps! apply]
/--
Definition of `toAddConstMapHom` / `toAddConstMapHom` 的定义

English:
definition toAddConstMapHom
  signature: : (G ≃+c[a, a] G) ->* (G ->+c[a, a] G) where
  body: toAddConstMap
  map_mul' _ _ := rfl
  map_one' := rfl

中文:
定义 toAddConstMapHom
  签名: : (G ≃+c[a, a] G) ->* (G ->+c[a, a] G) where
  定义体: toAddConstMap
  map_mul' _ _ := rfl
  map_one' := rfl

Depends on / 依赖: toAddConstMap
-/
def toAddConstMapHom : (G ≃+c[a, a] G) ->* (G ->+c[a, a] G) where
  toFun := toAddConstMap
  map_mul' _ _ := rfl
  map_one' := rfl

/-- Group equivalence between `G ≃+c[a, a] G` and the units of `G →+c[a, a] G`. -/
@[simps!]
/--
Definition of `equivUnits` / `equivUnits` 的定义

English:
definition equivUnits
  signature: : (G ≃+c[a, a] G) ≃* (G ->+c[a, a] G)ˣ where
  body: toAddConstMapHom.toHomUnits
  invFun u :=
    { toEquiv := Equiv.Perm.equivUnitsEnd.symm <| Units.map AddConstMap.toEnd u
      map_add_const' := u.1.2 }
  map_mul' _ _ := rfl

中文:
定义 equivUnits
  签名: : (G ≃+c[a, a] G) ≃* (G ->+c[a, a] G)ˣ where
  定义体: toAddConstMapHom.toHomUnits
  invFun u :=
    { toEquiv := Equiv.Perm.equivUnitsEnd.symm <| Units.map AddConstMap.toEnd u
      map_add_const' := u.1.2 }
  map_mul' _ _ := rfl

Depends on / 依赖: toAddConstMapHom, toAddConstMapHom.toHomUnits, toHomUnits
-/
def equivUnits : (G ≃+c[a, a] G) ≃* (G ->+c[a, a] G)ˣ where
  toFun := toAddConstMapHom.toHomUnits
  invFun u :=
    { toEquiv := Equiv.Perm.equivUnitsEnd.symm <| Units.map AddConstMap.toEnd u
      map_add_const' := u.1.2 }
  map_mul' _ _ := rfl

end AddConstEquiv
