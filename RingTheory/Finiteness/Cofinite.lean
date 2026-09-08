/-
Copyright (c) 2026 Martin Winter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Winter
-/
module

public import Mathlib.RingTheory.Noetherian.Basic

/-!
# Co-finitely generated submodules

This files defines the notion of a co-finitely generated submodule. A submodule `S` of a module
`M` is co-finitely generated (or CoFG for short) if the quotient of `M` by `S` is finitely
generated (i.e. FG).

## Main declarations

- `Submodule.CoFG` expresses that a submodule is co-finitely generated.

-/

public section

namespace Submodule

section Ring

variable {R : Type*} [Ring R]
variable {M : Type*} [AddCommGroup M] [Module R M]

/-- A submodule `S` of a module `M` is co-finitely generated (CoFG) if the quotient
  space `M ⧸ S` is finitely generated. -/
/-
**Submodule.CoFG** 是 Mathlib 中的一个缩写定义，位于命名空间 `Submodule`。
形式化陈述：CoFG (S : Submodule R M) : Prop
参数：S : Submodule R M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A submodule `S` of a module `M` is co-finitely generated (CoFG) if the quotient
  space `M ⧸ S` is finitely generated.
-/
abbrev CoFG (S : Submodule R M) : Prop := Module.Finite R (M ⧸ S)

/-- A submodule of a finite module is CoFG. -/
/-
**Submodule.CoFG.of_finite** 是 Mathlib 中的一个定理，位于命名空间 `Submodule.CoFG`。
形式化陈述：∀ {R : Type u_1} [inst : Ring R] {M : Type u_2} [inst_1 : AddCommGroup M] 
[inst_2 : _root_.Module R M]   [Module.Finite R M] {S : Submodule R M}, S.CoFG
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A submodule of a finite module is CoFG.
-/
@[simp] theorem CoFG.of_finite [Module.Finite R M] {S : Submodule R M} : S.CoFG :=
  Module.Finite.quotient R S

/-- The top submodule is CoFG. -/
/-
**Submodule.CoFG.top** 是 Mathlib 中的一个定理，位于命名空间 `Submodule.CoFG`。
形式化陈述：∀ {R : Type u_1} [inst : Ring R] {M : Type u_2} [inst_1 : AddCommGroup M] 
[inst_2 : _root_.Module R M], ⊤.CoFG
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.IsNoetherian.finite`：∀ (R : Type u_1) (M : Type u_3) [inst : Semi
ring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [IsNoetherian 
R M], Module.Fin…
· 使用定理 `isNoetherian_of_finite`：∀ (R : Type u_1) (M : Type u_3) [inst : Semiring
 R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] [Finite M],   IsNoet
herian R M
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α

--- 原说明 ---
The top submodule is CoFG.
-/
@[simp] theorem CoFG.top : (⊤ : Submodule R M).CoFG := inferInstance

variable (R M) in
/-- A module is finite if and only if the bottom submodule is CoFG. -/
/-
**Submodule._root_.Module.Finite.iff_cofg_bot** 是 Mathlib 中的一个定理，位于命名空间 `Submodu
le`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A module is finite if and only if the bottom submodule is CoFG.
-/
theorem _root_.Module.Finite.iff_cofg_bot : (⊥ : Submodule R M).CoFG ↔ Module.Finite R M :=
  ⟨fun _ => Module.Finite.equiv (quotEquivOfEqBot ⊥ rfl), fun _ => CoFG.of_finite⟩

/-- A complement of a CoFG submodule is FG. -/
/-
**Submodule.CoFG.fg_of_isCompl** 是 Mathlib 中的一个定理，位于命名空间 `Submodule.CoFG`。
形式化陈述：∀ {R : Type u_1} [inst : Ring R] {M : Type u_2} [inst_1 : AddCommGroup M] 
[inst_2 : _root_.Module R M]   {S T : Submodule R M}, IsCompl S T → S.CoFG → T.F
G
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Module.Finite.iff_fg`：iff_fg {N : Submodule R M} : Module.Finite R N ↔ N
.FG
· 使用定理 `Module.Finite.equiv`：equiv [Module.Finite R M] (e : M ≃ₗ[R] N) : Module.
Finite R N

--- 原说明 ---
A complement of a CoFG submodule is FG.
-/
theorem CoFG.fg_of_isCompl {S T : Submodule R M} (hST : IsCompl S T) (hS : S.CoFG) : T.FG :=
  Module.Finite.iff_fg.mp <| Module.Finite.equiv <| quotientEquivOfIsCompl S T hST

/-- Over a noetherian ring, if `S` and `T` are disjoint and `T` is CoFG, then `S` is FG. -/
/-
**Submodule.CoFG.fg_of_disjoint** 是 Mathlib 中的一个定理，位于命名空间 `Submodule.CoFG`。
形式化陈述：∀ {R : Type u_1} [inst : Ring R] {M : Type u_2} [inst_1 : AddCommGroup M] 
[inst_2 : _root_.Module R M]   [IsNoetherianRing R] {S T : Submodule R M}, Disjo
int S T → T.CoFG → S.FG
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.FG.of_disjoint_of_isNoetherian_quotient`：∀ {R : Type u_1} {M :
 Type u_2} [inst : Ring R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M
]   {S T : Submodule R M} [IsNoetherian…

--- 原说明 ---
Over a noetherian ring, if `S` and `T` are disjoint and `T` is CoFG, then `S` is
 FG.
-/
theorem CoFG.fg_of_disjoint [IsNoetherianRing R] {S T : Submodule R M} (hST : Disjoint S T)
    (hT : T.CoFG) : S.FG :=
  .of_disjoint_of_isNoetherian_quotient hST

/-- If `S` and `T` are co-disjoint and `S` is FG, then `T` is CoFG. -/
/-
**Submodule.FG.cofg_of_codisjoint** 是 Mathlib 中的一个定理，位于命名空间 `Submodule.FG`。
形式化陈述：∀ {R : Type u_1} [inst : Ring R] {M : Type u_2} [inst_1 : AddCommGroup M] 
[inst_2 : _root_.Module R M]   {S T : Submodule R M}, Codisjoint S T → S.FG → T.
CoFG
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Module.Finite.iff_fg`：iff_fg {N : Submodule R M} : Module.Finite R N ↔ N
.FG
· 使用定理 `Module.Finite.of_surjective`：of_surjective [hM : Module.Finite R M] (f :
 M ->ₛₗ[σ] P) (hf : Surjective f) : Module.Finite S P
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.range_domRestrict`：∀ {R : Type u_1} {R₂ : Type u_2} {M : Type 
u_5} {M₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : AddC
ommMonoid M] [ins…
· 使用定理 `Codisjoint.eq_top`：∀ {α : Type u_1} [inst : SemilatticeSup α] [inst_1 : 
OrderTop α] {a b : α}, Codisjoint a b → a ⊔ b = ⊤
· 使用定理 `Codisjoint.symm`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Orde
rTop α] ⦃a b : α⦄, Codisjoint a b → Codisjoint b a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If `S` and `T` are co-disjoint and `S` is FG, then `T` is CoFG.
-/
theorem FG.cofg_of_codisjoint {S T : Submodule R M} (hST : Codisjoint S T) (hS : S.FG) :
    T.CoFG :=
  have := Module.Finite.iff_fg.mpr hS
  .of_surjective (T.mkQ.domRestrict S) (by simp [← LinearMap.range_eq_top, hST.symm.eq_top])

/-- A complement of an FG submodule is CoFG. -/
/-
**Submodule.FG.cofg_of_isCompl** 是 Mathlib 中的一个定理，位于命名空间 `Submodule.FG`。
形式化陈述：∀ {R : Type u_1} [inst : Ring R] {M : Type u_2} [inst_1 : AddCommGroup M] 
[inst_2 : _root_.Module R M]   {S T : Submodule R M}, IsCompl S T → S.FG → T.CoF
G
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.FG.cofg_of_codisjoint`：∀ {R : Type u_1} [inst : Ring R] {M : T
ype u_2} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   {S T : Submodu
le R M}, Codisjoint S…
· 使用定理 `IsCompl.codisjoint`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : B
oundedOrder α] {x y : α}, IsCompl x y → Codisjoint x y

--- 原说明 ---
A complement of an FG submodule is CoFG.
-/
theorem FG.cofg_of_isCompl {S T : Submodule R M} (hST : IsCompl S T) (hS : S.FG) : T.CoFG :=
  hS.cofg_of_codisjoint hST.codisjoint

/-- A submodule that contains a CoFG submodule is CoFG. -/
/-
**Submodule.CoFG.of_le** 是 Mathlib 中的一个定理，位于命名空间 `Submodule.CoFG`。
形式化陈述：∀ {R : Type u_1} [inst : Ring R] {M : Type u_2} [inst_1 : AddCommGroup M] 
[inst_2 : _root_.Module R M]   {S T : Submodule R M}, S ≤ T → S.CoFG → T.CoFG
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sup_eq_right`：sup_eq_right : a ⊔ b = b ↔ a <= b
· 使用定理 `Module.Finite.equiv`：equiv [Module.Finite R M] (e : M ≃ₗ[R] N) : Module.
Finite R N

--- 原说明 ---
A submodule that contains a CoFG submodule is CoFG.
-/
theorem CoFG.of_le {S T : Submodule R M} (hT : S ≤ T) (hS : S.CoFG) : T.CoFG := by
  rw [← sup_eq_right.mpr hT]
  exact Module.Finite.equiv (quotientQuotientEquivQuotientSup S T)

@[deprecated (since := "2026-05-13")]
alias CoFG.cofg_of_le := CoFG.of_le

section LinearMap

open LinearMap

variable {N : Type*} [AddCommGroup N] [Module R N]

/-- The range of a linear map is FG if and only if the kernel is CoFG. -/
/-
**Submodule.range_fg_iff_ker_cofg** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：range_fg_iff_ker_cofg {f : M ->ₗ[R] N} : (range f).FG ↔ (ker f).CoFG
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.Finite.iff_fg`：iff_fg {N : Submodule R M} : Module.Finite R N ↔ N
.FG
· 使用定理 `Module.Finite.equiv_iff`：equiv_iff (e : M ≃ₗ[R] N) : Module.Finite R M ↔
 Module.Finite R N

--- 原说明 ---
The range of a linear map is FG if and only if the kernel is CoFG.
-/
theorem range_fg_iff_ker_cofg {f : M →ₗ[R] N} : (range f).FG ↔ (ker f).CoFG := by
  rw [← Module.Finite.iff_fg]
  exact Module.Finite.equiv_iff <| f.quotKerEquivRange.symm

/-- The kernel of a linear map into a noetherian module is CoFG. -/
/-
**Submodule.CoFG.ker** 是 Mathlib 中的一个定理，位于命名空间 `Submodule.CoFG`。
形式化陈述：∀ {R : Type u_1} [inst : Ring R] {M : Type u_2} [inst_1 : AddCommGroup M] 
[inst_2 : _root_.Module R M] {N : Type u_3}   [inst_3 : AddCommGroup N] [inst_4 
: _root_.Module R N] [IsNoetherian R N] (f : M →ₗ[R] N), f.ker.CoFG
参数：f : M →ₗ[R] N。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.range_fg_iff_ker_cofg`：range_fg_iff_ker_cofg {f : M ->ₗ[R] N} 
: (range f).FG ↔ (ker f).CoFG
· 使用定理 `IsNoetherian.noetherian`：∀ {R : Type u_1} {M : Type u_2} {inst : Semirin
g R} {inst_1 : AddCommMonoid M} {inst_2 : _root_.Module R M}   [self : IsNoether
ian R M] (s :…

--- 原说明 ---
The kernel of a linear map into a noetherian module is CoFG.
-/
protected theorem CoFG.ker [IsNoetherian R N] (f : M →ₗ[R] N) : (ker f).CoFG :=
  range_fg_iff_ker_cofg.mp <| IsNoetherian.noetherian _

end LinearMap

section IsNoetherianRing

variable [IsNoetherianRing R]

/-- Over a noetherian ring the intersection of two CoFG submodules is CoFG. -/
/-
**Submodule.CoFG.inf** 是 Mathlib 中的一个定理，位于命名空间 `Submodule.CoFG`。
形式化陈述：∀ {R : Type u_1} [inst : Ring R] {M : Type u_2} [inst_1 : AddCommGroup M] 
[inst_2 : _root_.Module R M]   [IsNoetherianRing R] {S T : Submodule R M}, S.CoF
G → T.CoFG → (S ⊓ T).CoFG
参数：S ⊓ T。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.ker_mkQ`：ker_mkQ : ker p.mkQ = p
· 使用定理 `LinearMap.ker_prod`：ker_prod (f : M ->ₗ[R] M₂) (g : M ->ₗ[R] M₃) : ker (
prod f g) = ker f ⊓ ker g
· 使用定理 `Submodule.CoFG.ker`：∀ {R : Type u_1} [inst : Ring R] {M : Type u_2} [ins
t_1 : AddCommGroup M] [inst_2 : _root_.Module R M] {N : Type u_3}   [inst_3 : Ad
dCommGro…

--- 原说明 ---
Over a noetherian ring the intersection of two CoFG submodules is CoFG.
-/
theorem CoFG.inf {S T : Submodule R M} (hS : S.CoFG) (hT : T.CoFG) :
      (S ⊓ T).CoFG := by
  rw [← Submodule.ker_mkQ S, ← Submodule.ker_mkQ T, ← LinearMap.ker_prod]
  exact CoFG.ker _

/-- Over a noetherian ring the infimum of a finite family of CoFG submodules is CoFG. -/
/-
**Submodule.CoFG.sInf** 是 Mathlib 中的一个定理，位于命名空间 `Submodule.CoFG`。
形式化陈述：∀ {R : Type u_1} [inst : Ring R] {M : Type u_2} [inst_1 : AddCommGroup M] 
[inst_2 : _root_.Module R M]   [IsNoetherianRing R] {s : Finset (Submodule R M)}
, (∀ S ∈ s, S.CoFG) → (sInf ↑s).CoFG
参数：Submodule R M；∀ S ∈ s, S.CoFG；sInf ↑s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst : De
cidableEq α],   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → motive s → motive 
(inser…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_empty`：coe_empty : ((∅ : Finset α) : Set α) = ∅
· 使用定理 `sInf_empty`：∀ {α : Type u_1} [inst : CompleteLattice α], sInf ∅ = ⊤
· 使用定理 `Finset.coe_insert`：coe_insert (a : α) (s : Finset α) : ↑(insert a s) = (
insert a s : Set α)
· 使用定理 `sInf_insert`：∀ {α : Type u_1} [inst : CompleteLattice α] {a : α} {s : Se
t α}, sInf (insert a s) = a ⊓ sInf s
· 使用定理 `Submodule.CoFG.inf`：∀ {R : Type u_1} [inst : Ring R] {M : Type u_2} [ins
t_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsNoetherianRing R] {S T :
 Submodu…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
Over a noetherian ring the infimum of a finite family of CoFG submodules is CoFG
.
-/
protected theorem CoFG.sInf {s : Finset (Submodule R M)} (hs : ∀ S ∈ s, S.CoFG) :
    (sInf (s : Set (Submodule R M))).CoFG := by
  induction s using Finset.induction with
  | empty => simp
  | insert w s hws hs' =>
    simp only [Finset.mem_insert, forall_eq_or_imp, Finset.coe_insert, sInf_insert] at *
    exact hs.1.inf (hs' hs.2)

/-- Over a noetherian ring the infimum of a finite family of CoFG submodules is CoFG. -/
/-
**Submodule.CoFG.sInf_of_finite** 是 Mathlib 中的一个定理，位于命名空间 `Submodule.CoFG`。
形式化陈述：∀ {R : Type u_1} [inst : Ring R] {M : Type u_2} [inst_1 : AddCommGroup M] 
[inst_2 : _root_.Module R M]   [IsNoetherianRing R] {s : Set (Submodule R M)}, s
.Finite → (∀ S ∈ s, S.CoFG) → (sInf s).CoFG
参数：Submodule R M；∀ S ∈ s, S.CoFG；sInf s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.Finite.coe_toFinset`：∀ {α : Type u} {s : Set α} (hs : s.Finite), ↑hs
.toFinset = s
· 使用定理 `Submodule.CoFG.sInf`：∀ {R : Type u_1} [inst : Ring R] {M : Type u_2} [in
st_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsNoetherianRing R] {s : 
Finset (S…

--- 原说明 ---
Over a noetherian ring the infimum of a finite family of CoFG submodules is CoFG
.
-/
theorem CoFG.sInf_of_finite {s : Set (Submodule R M)} (hs : s.Finite)
    (hcofg : ∀ S ∈ s, S.CoFG) : (sInf s).CoFG := by
  rw [← hs.coe_toFinset] at hcofg ⊢; exact CoFG.sInf hcofg

end IsNoetherianRing

end Ring

end Submodule

