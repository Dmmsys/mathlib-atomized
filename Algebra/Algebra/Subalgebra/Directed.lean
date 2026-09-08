/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.Data.Set.UnionLift

/-!
# Subalgebras and directed Unions of sets

## Main results

* `Subalgebra.coe_iSup_of_directed`: a directed supremum consists of the union of the algebras
* `Subalgebra.iSupLift`: define an algebra homomorphism on a directed supremum of subalgebras by
  defining it on each subalgebra, and proving that it agrees on the intersection of subalgebras.
-/

@[expose] public section

namespace Subalgebra

open Algebra

variable {R A B : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]
variable (S : Subalgebra R A)

variable {ι : Type*} [Nonempty ι] {K : ι → Subalgebra R A}

/-
**Subalgebra.coe_iSup_of_directed** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：coe_iSup_of_directed (dir : Directed (· <= ·) K) : ↑(iSup K) = ⋃ i, (K i :
 Set A)
参数：dir : Directed (· <= ·) K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subsemiring.coe_iSup_of_directed`：coe_iSup_of_directed {ι} [hι : Nonempt
y ι] {S : ι -> Subsemiring R} (hS : Directed (· <= ·) S) : ((⨆ i, S i : Subsemir
ing R) : Set R) = ⋃ i,…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.mem_iUnion`：mem_iUnion {x : α} {s : ι -> Set α} : (x in ⋃ i, s i) ↔ 
exists i, x in s i
· 使用定理 `Subalgebra.algebraMap_mem`：∀ {R : Type u} {A : Type v} [inst : CommSemir
ing R] [inst_1 : Semiring A] [inst_2 : Algebra R A] (S : Subalgebra R A)   (r : 
R), (algebraMap…
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `iSup_le`：iSup_le (h : forall i, f i <= a) : iSup f <= a
· 使用定理 `le_iSup`：le_iSup (f : ι -> α) (i : ι) : f i <= iSup f
· 使用定理 `Set.iUnion_subset`：iUnion_subset {s : ι -> Set α} {t : Set α} (h : foral
l i, s i subseteq t) : ⋃ i, s i subseteq t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subsemiring.coe_copy`：∀ {R : Type u} [inst : NonAssocSemiring R] (S : Su
bsemiring R) (s : Set R) (hs : s = ↑S), ↑(S.copy s hs) = s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coe_iSup_of_directed (dir : Directed (· ≤ ·) K) : ↑(iSup K) = ⋃ i, (K i : Set A) := by
  let s : Subalgebra R A :=
    { __ := Subsemiring.copy _ _ (Subsemiring.coe_iSup_of_directed dir).symm
      algebraMap_mem' := fun _ ↦ Set.mem_iUnion.2
        ⟨Classical.arbitrary ι, Subalgebra.algebraMap_mem _ _⟩ }
  have : iSup K = s := le_antisymm
    (iSup_le fun i ↦ le_iSup (fun i ↦ (K i : Set A)) i) (Set.iUnion_subset fun _ ↦ le_iSup K _)
  simp [this, s]
/-
**Subalgebra.isMulCommutative_iSup** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：isMulCommutative_iSup {S : ι -> Subalgebra R A} [hS : forall i, IsMulCommu
tative (S i)] (dir : Directed (· <= ·) S) : IsMulCommutative (⨆ i, S i : Subalge
bra R A)
参数：S i；dir : Directed (· <= ·) S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.substr`：∀ {α : Sort u} {p : α → Prop} {a b : α}, b = a → p a → p b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subalgebra.coe_iSup_of_directed`：coe_iSup_of_directed (dir : Directed (·
 <= ·) K) : ↑(iSup K) = ⋃ i, (K i : Set A)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `forall_prop_domain_congr`：∀ {p₁ p₂ : Prop} {q₁ : p₁ → Prop} {q₂ : p₂ → P
rop} (h₁ : p₁ = p₂),   (∀ (a : p₂), q₁ ⋯ = q₂ a) → (∀ (a : p₁), q₁ a) = ∀ (a : p
₂), q₂ a
· 使用定理 `MulMemClass.mul_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Mul M} {inst_1 : SetLike S M} [self : MulMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `SubmonoidClass.toMulMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   Mu
lMemClass S M
· 使用定理 `SubsemiringClass.toSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Type 
u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringClas
s S R], SubmonoidClass …
· 使用定理 `Subalgebra.instSubsemiringClass`：∀ {R : Type u} {A : Type v} [inst : Com
mSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SubsemiringClass (S
ubalgebra R A) A
· 使用定理 `Subtype.mk.injEq`：∀ {α : Sort u} {p : α → Prop} (val : α) (property : p 
val) (val_1 : α) (property_1 : p val_1),   (⟨val, property⟩ = ⟨val_1, property_1
⟩) = (…
· 使用定理 `Subsemiring.coe_iSup_of_directed`：coe_iSup_of_directed {ι} [hι : Nonempt
y ι] {S : ι -> Subsemiring R} (hS : Directed (· <= ·) S) : ((⨆ i, S i : Subsemir
ing R) : Set R) = ⋃ i,…
· 使用定理 `NonUnitalSubsemiringClass.mulMemClass`：∀ (S : Type u_1) (R : Type u) [in
st : NonUnitalNonAssocSemiring R] [inst_1 : SetLike S R]   [h : NonUnitalSubsemi
ringClass S R], MulMemClass…
· 使用定理 `SubsemiringClass.nonUnitalSubsemiringClass`：∀ (S : Type u_1) (R : Type u
) [inst : NonAssocSemiring R] [inst_1 : SetLike S R] [SubsemiringClass S R],   N
onUnitalSubsemiringClass S R
· 使用定理 `Subsemiring.instSubsemiringClass`：∀ {R : Type u} [inst : NonAssocSemirin
g R], SubsemiringClass (Subsemiring R) R
· 使用定理 `Subsemiring.isMulCommutative_iSup`：isMulCommutative_iSup {ι : Sort*} [No
nempty ι] {S : ι -> Subsemiring R} [hS : forall i, IsMulCommutative (S i)] (dir 
: Directed (· <= ·) S) …
-/
theorem isMulCommutative_iSup {S : ι → Subalgebra R A}
    [hS : ∀ i, IsMulCommutative (S i)] (dir : Directed (· ≤ ·) S) :
    IsMulCommutative (⨆ i, S i : Subalgebra R A) := by
  simpa [isMulCommutative_iff, ← SetLike.mem_coe, coe_iSup_of_directed dir,
    Subsemiring.coe_iSup_of_directed dir] using Subsemiring.isMulCommutative_iSup dir
/-
**Subalgebra.instIsMulCommutative_iSup** 是 Mathlib 中的一个实例，位于命名空间 `Subalgebra`。
形式化陈述：instIsMulCommutative_iSup [Preorder ι] [IsDirectedOrder ι] {S : ι ->o Suba
lgebra R A} [hS : forall i, IsMulCommutative (S i)] : IsMulCommutative (⨆ i, S i
 : Subalgebra R A)
参数：S i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Subalgebra.isMulCommutative_iSup`：isMulCommutative_iSup {S : ι -> Subalg
ebra R A} [hS : forall i, IsMulCommutative (S i)] (dir : Directed (· <= ·) S) : 
IsMulCommutative (⨆ i,…
· 使用定理 `Monotone.directed_le`：Monotone.directed_le [Preorder α] [IsDirectedOrder
 α] [Preorder β] {f : α -> β} : Monotone f -> Directed (· <= ·) f
· 使用定理 `OrderHom.monotone`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] [
inst_1 : Preorder β] (f : α →o β), Monotone ⇑f
-/
instance instIsMulCommutative_iSup [Preorder ι] [IsDirectedOrder ι]
    {S : ι →o Subalgebra R A} [hS : ∀ i, IsMulCommutative (S i)] :
    IsMulCommutative (⨆ i, S i : Subalgebra R A) :=
  isMulCommutative_iSup S.monotone.directed_le

variable (K)

/-- Define an algebra homomorphism on a directed supremum of subalgebras by defining
it on each subalgebra, and proving that it agrees on the intersection of subalgebras. -/
/-
**Subalgebra.iSupLift** 是 Mathlib 中的一个定义，位于命名空间 `Subalgebra`。
形式化陈述：iSupLift (dir : Directed (· <= ·) K) (f : forall i, K i ->ₐ[R] B) (hf : fo
rall (i j : ι) (h : K i <= K j), f i = (f j).comp (inclusion h)) (T : Subalgebra
 R A) (hT : T <= iSup K) : ↥T ->ₐ[R] B
参数：dir : Directed (· <= ·) K；f : forall i, K i ->ₐ[R] B；hf : forall (i j : ι) (h
 : K i <= K j), f i = (f j).comp (inclusion h)；T : Subalgebra R A；hT : T <= iSup
 K。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Define an algebra homomorphism on a directed supremum of subalgebras by defining
it on each subalgebra, and proving that it agrees on the intersection of subalge
bras.
-/
noncomputable def iSupLift (dir : Directed (· ≤ ·) K) (f : ∀ i, K i →ₐ[R] B)
    (hf : ∀ (i j : ι) (h : K i ≤ K j), f i = (f j).comp (inclusion h))
    (T : Subalgebra R A) (hT : T ≤ iSup K) : ↥T →ₐ[R] B := by
  let compat :
      ∀ (i j) (x : A) (hxi : x ∈ (K i : Set A)) (hxj : x ∈ (K j : Set A)),
        f i ⟨x, hxi⟩ = f j ⟨x, hxj⟩ := by
    intro i j x hxi hxj
    rcases dir i j with ⟨k, hik, hjk⟩
    simp [hf i k hik, hf j k hjk]
  let liftSup : ((iSup K : Subalgebra R A)) →ₐ[R] B :=
    { toFun :=
        Set.iUnionLift (fun i => ↑(K i)) (fun i x => f i x) compat
          ((iSup K : Subalgebra R A) : Set A)
          (le_of_eq <| coe_iSup_of_directed (K := K) dir)
      map_one' := by
        dsimp
        exact Set.iUnionLift_const _ (fun i : ι => (1 : K i)) (fun _ => rfl) _ (by simp)
      map_zero' := by
        dsimp
        exact Set.iUnionLift_const _ (fun i : ι => (0 : K i)) (fun _ => rfl) _ (by simp)
      map_mul' := by
        dsimp
        apply Set.iUnionLift_binary (coe_iSup_of_directed (K := K) dir) dir _ (fun _ => (· * ·))
        all_goals simp
      map_add' := by
        dsimp
        apply Set.iUnionLift_binary (coe_iSup_of_directed (K := K) dir) dir _ (fun _ => (· + ·))
        all_goals simp
      commutes' := fun r => by
        dsimp
        exact
          Set.iUnionLift_const _ (fun i : ι => algebraMap R (K i) r) (fun _ => rfl) _ (by simp) }
  exact liftSup.comp (inclusion hT)


set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**Subalgebra.iSupLift_inclusion** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：iSupLift_inclusion {dir : Directed (· <= ·) K} {f : forall i, K i ->ₐ[R] B
} {hf : forall (i j : ι) (h : K i <= K j), f i = (f j).comp (inclusion h)} {T : 
Subalgebra R A} {hT : T <= iSup K} {i : ι} (x : K i) (h : K i <= T) : iSupLift K
 dir f hf T hT (inclusion h x) = f i x
参数：· <= ·；i j : ι；h : K i <= K j；f j；inclusion h；x : K i；h : K i <= T。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `SetLike.coe_subset_coe`：∀ {A : Type u_1} {B : Type u_2} [inst : SetLike 
A B] [inst_1 : LE A] [IsConcreteLE A B] {S T : A}, ↑S ⊆ ↑T ↔ S ≤ T
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.iUnionLift_inclusion`：iUnionLift_inclusion {i : ι} (x : S i) (h : S 
i subseteq T) : iUnionLift S f hf T hT (Set.inclusion h x) = f i x
-/
theorem iSupLift_inclusion {dir : Directed (· ≤ ·) K} {f : ∀ i, K i →ₐ[R] B}
    {hf : ∀ (i j : ι) (h : K i ≤ K j), f i = (f j).comp (inclusion h)}
    {T : Subalgebra R A} {hT : T ≤ iSup K} {i : ι} (x : K i) (h : K i ≤ T) :
    iSupLift K dir f hf T hT (inclusion h x) = f i x := by
  dsimp [iSupLift, inclusion]
  rw [Set.iUnionLift_inclusion]
  exact SetLike.coe_subset_coe.mpr <| h.trans hT

@[simp]
/-
**Subalgebra.iSupLift_comp_inclusion** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：iSupLift_comp_inclusion {dir : Directed (· <= ·) K} {f : forall i, K i ->ₐ
[R] B} {hf : forall (i j : ι) (h : K i <= K j), f i = (f j).comp (inclusion h)} 
{T : Subalgebra R A} {hT : T <= iSup K} {i : ι} (h : K i <= T) : (iSupLift K dir
 f hf T hT).comp (inclusion h) = f i
参数：· <= ·；i j : ι；h : K i <= K j；f j；inclusion h；h : K i <= T。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHom.ext`：ext {φ₁ φ₂ : A ->ₐ[R] B} (H : forall x, φ₁ x = φ₂ x) : φ₁ = 
φ₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subalgebra.iSupLift_inclusion`：iSupLift_inclusion {dir : Directed (· <= 
·) K} {f : forall i, K i ->ₐ[R] B} {hf : forall (i j : ι) (h : K i <= K j), f i 
= (f j).comp (inclu…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem iSupLift_comp_inclusion {dir : Directed (· ≤ ·) K} {f : ∀ i, K i →ₐ[R] B}
    {hf : ∀ (i j : ι) (h : K i ≤ K j), f i = (f j).comp (inclusion h)}
    {T : Subalgebra R A} {hT : T ≤ iSup K} {i : ι} (h : K i ≤ T) :
    (iSupLift K dir f hf T hT).comp (inclusion h) = f i := by ext; simp

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**Subalgebra.iSupLift_mk** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：iSupLift_mk {dir : Directed (· <= ·) K} {f : forall i, K i ->ₐ[R] B} {hf :
 forall (i j : ι) (h : K i <= K j), f i = (f j).comp (inclusion h)} {T : Subalge
bra R A} {hT : T <= iSup K} {i : ι} (x : K i) (hx : (x : A) in T) : iSupLift K d
ir f hf T hT ⟨x, hx⟩ = f i x
参数：· <= ·；i j : ι；h : K i <= K j；f j；inclusion h；x : K i；hx : (x : A) in T。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.iUnionLift_mk`：iUnionLift_mk {i : ι} (x : S i) (hx : (x : α) in T) :
 iUnionLift S f hf T hT ⟨x, hx⟩ = f i x
-/
theorem iSupLift_mk {dir : Directed (· ≤ ·) K} {f : ∀ i, K i →ₐ[R] B}
    {hf : ∀ (i j : ι) (h : K i ≤ K j), f i = (f j).comp (inclusion h)}
    {T : Subalgebra R A} {hT : T ≤ iSup K} {i : ι} (x : K i) (hx : (x : A) ∈ T) :
    iSupLift K dir f hf T hT ⟨x, hx⟩ = f i x := by
  dsimp [iSupLift, inclusion]
  rw [Set.iUnionLift_mk]

set_option backward.isDefEq.respectTransparency false in
/-
**Subalgebra.iSupLift_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：iSupLift_of_mem {dir : Directed (· <= ·) K} {f : forall i, K i ->ₐ[R] B} {
hf : forall (i j : ι) (h : K i <= K j), f i = (f j).comp (inclusion h)} {T : Sub
algebra R A} {hT : T <= iSup K} {i : ι} (x : T) (hx : (x : A) in K i) : iSupLift
 K dir f hf T hT x = f i ⟨x, hx⟩
参数：· <= ·；i j : ι；h : K i <= K j；f j；inclusion h；x : T；hx : (x : A) in K i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.iUnionLift_of_mem`：iUnionLift_of_mem (x : T) {i : ι} (hx : (x : α) i
n S i) : iUnionLift S f hf T hT x = f i ⟨x, hx⟩
-/
theorem iSupLift_of_mem {dir : Directed (· ≤ ·) K} {f : ∀ i, K i →ₐ[R] B}
    {hf : ∀ (i j : ι) (h : K i ≤ K j), f i = (f j).comp (inclusion h)}
    {T : Subalgebra R A} {hT : T ≤ iSup K} {i : ι} (x : T) (hx : (x : A) ∈ K i) :
    iSupLift K dir f hf T hT x = f i ⟨x, hx⟩ := by
  dsimp [iSupLift, inclusion]
  rw [Set.iUnionLift_of_mem]

end Subalgebra

