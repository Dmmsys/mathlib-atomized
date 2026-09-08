/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Kevin Buzzard, Yury Kudryashov
-/
module

public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.LinearAlgebra.Span.Basic

/-!
# Quotients by submodules

* If `p` is a submodule of `M`, `M ⧸ p` is the quotient of `M` with respect to `p`:
  that is, elements of `M` are identified if their difference is in `p`. This is itself a module.

## Main definitions

* `Submodule.Quotient.restrictScalarsEquiv`: The quotient of `P` as an `S`-submodule is the same
  as the quotient of `P` as an `R`-submodule,
* `Submodule.liftQ`: lift a map `M → M₂` to a map `M ⧸ p → M₂` if the kernel is contained in `p`
* `Submodule.mapQ`: lift a map `M → M₂` to a map `M ⧸ p → M₂ ⧸ q` if the image of `p` is contained
  in `q`

-/

@[expose] public section

assert_not_exists Cardinal

-- For most of this file we work over a noncommutative ring
section Ring

namespace Submodule

variable {R M : Type*} {r : R} {x y : M} [Ring R] [AddCommGroup M] [Module R M]
variable (p p' p'' : Submodule R M)

open LinearMap QuotientAddGroup

namespace Quotient

section Module

variable (S : Type*)

/-- The quotient of `P` as an `S`-submodule is the same as the quotient of `P` as an `R`-submodule,
where `P : Submodule R M`.
-/
/-
**Submodule.Quotient.restrictScalarsEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Submodule.Q
uotient`。
形式化陈述：restrictScalarsEquiv [Ring S] [SMul S R] [Module S M] [IsScalarTower S R M
] (P : Submodule R M) : (M ⧸ P.restrictScalars S) ≃ₗ[S] M ⧸ P
参数：P : Submodule R M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The quotient of `P` as an `S`-submodule is the same as the quotient of `P` as an
 `R`-submodule,
where `P : Submodule R M`.
-/
def restrictScalarsEquiv [Ring S] [SMul S R] [Module S M] [IsScalarTower S R M]
    (P : Submodule R M) : (M ⧸ P.restrictScalars S) ≃ₗ[S] M ⧸ P :=
  { Quotient.congrRight fun _ _ => Iff.rfl with
    map_add' := fun x y => Quotient.inductionOn₂' x y fun _x' _y' => rfl
    map_smul' := fun _c x => Submodule.Quotient.induction_on _ x fun _x' => rfl }

@[simp]
/-
**Submodule.Quotient.restrictScalarsEquiv_mk** 是 Mathlib 中的一个定理，位于命名空间 `Submodul
e.Quotient`。
形式化陈述：restrictScalarsEquiv_mk [Ring S] [SMul S R] [Module S M] [IsScalarTower S 
R M] (P : Submodule R M) (x : M) : restrictScalarsEquiv S P (mk x) = mk x
参数：P : Submodule R M；x : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem restrictScalarsEquiv_mk [Ring S] [SMul S R] [Module S M] [IsScalarTower S R M]
    (P : Submodule R M) (x : M) :
    restrictScalarsEquiv S P (mk x) = mk x :=
  rfl

@[simp]
/-
**Submodule.Quotient.restrictScalarsEquiv_symm_mk** 是 Mathlib 中的一个定理，位于命名空间 `Sub
module.Quotient`。
形式化陈述：restrictScalarsEquiv_symm_mk [Ring S] [SMul S R] [Module S M] [IsScalarTow
er S R M] (P : Submodule R M) (x : M) : (restrictScalarsEquiv S P).symm (mk x) =
 mk x
参数：P : Submodule R M；x : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem restrictScalarsEquiv_symm_mk [Ring S] [SMul S R] [Module S M] [IsScalarTower S R M]
    (P : Submodule R M) (x : M) :
    (restrictScalarsEquiv S P).symm (mk x) = mk x :=
  rfl

end Module

variable {p}

/-
**Submodule.Quotient.nontrivial_iff** 是 Mathlib 中的一个定理，位于命名空间 `Submodule.Quotien
t`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} [inst : Ring R] [inst_1 : AddCommGroup M] 
[inst_2 : _root_.Module R M]   {p : Submodule R M}, Nontrivial (M ⧸ p) ↔ p ≠ ⊤
参数：M ⧸ p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `QuotientAddGroup.nontrivial_iff`：∀ {G : Type u_1} [inst : AddGroup G] {N
 : AddSubgroup G}, Nontrivial (G ⧸ N) ↔ N ≠ ⊤
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] protected lemma nontrivial_iff : Nontrivial (M ⧸ p) ↔ p ≠ ⊤ :=
  QuotientAddGroup.nontrivial_iff.trans (by simp)
/-
**Submodule.Quotient.subsingleton_iff** 是 Mathlib 中的一个定理，位于命名空间 `Submodule.Quoti
ent`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} [inst : Ring R] [inst_1 : AddCommGroup M] 
[inst_2 : _root_.Module R M]   {p : Submodule R M}, Subsingleton (M ⧸ p) ↔ p = ⊤
参数：M ⧸ p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `QuotientAddGroup.subsingleton_iff`：∀ {G : Type u_1} [inst : AddGroup G] 
{N : AddSubgroup G}, Subsingleton (G ⧸ N) ↔ N = ⊤
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] protected lemma subsingleton_iff : Subsingleton (M ⧸ p) ↔ p = ⊤ :=
  QuotientAddGroup.subsingleton_iff.trans (by simp)
/-
**Submodule.Quotient.** 是 Mathlib 中的一个实例，位于命名空间 `Submodule.Quotient`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Subsingleton M] : Subsingleton (M ⧸ p) := by simpa using Subsingleton.elim ..

end Quotient

/-
**Submodule.QuotientBot.infinite** 是 Mathlib 中的一个定理，位于命名空间 `Submodule.QuotientBo
t`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} [inst : Ring R] [inst_1 : AddCommGroup M] 
[inst_2 : _root_.Module R M] [Infinite M],   Infinite (M ⧸ ⊥)
参数：M ⧸ ⊥。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Infinite.of_injective`：of_injective {α β} [Infinite β] (f : β -> α) (hf 
: Injective f) : Infinite α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `Submodule.Quotient.eq`：∀ {R : Type u_1} {M : Type u_2} [inst : Ring R] [
inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   (p : Submodule R M) {x y
 : M}, Subm…
-/
instance QuotientBot.infinite [Infinite M] : Infinite (M ⧸ (⊥ : Submodule R M)) :=
  Infinite.of_injective Submodule.Quotient.mk fun _x _y h =>
    sub_eq_zero.mp <| (Submodule.Quotient.eq ⊥).mp h
/-
**Submodule.QuotientTop.unique** 是 Mathlib 中的一个定义，位于命名空间 `Submodule.QuotientTop`
。
形式化陈述：{R : Type u_1} →   {M : Type u_2} → [inst : Ring R] → [inst_1 : AddCommGro
up M] → [inst_2 : _root_.Module R M] → Unique (M ⧸ ⊤)
参数：M ⧸ ⊤。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance QuotientTop.unique : Unique (M ⧸ (⊤ : Submodule R M)) where
  default := 0
  uniq x := Submodule.Quotient.induction_on _ x fun _x =>
    (Submodule.Quotient.eq ⊤).mpr Submodule.mem_top
/-
**Submodule.QuotientTop.fintype** 是 Mathlib 中的一个定义，位于命名空间 `Submodule.QuotientTop
`。
形式化陈述：{R : Type u_1} →   {M : Type u_2} → [inst : Ring R] → [inst_1 : AddCommGro
up M] → [inst_2 : _root_.Module R M] → Fintype (M ⧸ ⊤)
参数：M ⧸ ⊤。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance QuotientTop.fintype : Fintype (M ⧸ (⊤ : Submodule R M)) :=
  Fintype.ofSubsingleton 0

variable {p} in
/-
**Submodule.unique_quotient_iff_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：unique_quotient_iff_eq_top : Nonempty (Unique (M ⧸ p)) ↔ p = ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.Quotient.subsingleton_iff`：∀ {R : Type u_1} {M : Type u_2} [in
st : Ring R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   {p : Submo
dule R M}, Subsingleton (…
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem unique_quotient_iff_eq_top : Nonempty (Unique (M ⧸ p)) ↔ p = ⊤ :=
  ⟨fun ⟨h⟩ => Quotient.subsingleton_iff.mp (@Unique.instSubsingleton _ h),
    by rintro rfl; exact ⟨QuotientTop.unique⟩⟩
/-
**Submodule.Quotient.fintype** 是 Mathlib 中的一个定义，位于命名空间 `Submodule.Quotient`。
形式化陈述：{R : Type u_1} →   {M : Type u_2} →     [inst : Ring R] →       [inst_1 : 
AddCommGroup M] → [inst_2 : _root_.Module R M] → [Fintype M] → (S : Submodule R 
M) → Fintype (M ⧸ S)
参数：S : Submodule R M；M ⧸ S。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance Quotient.fintype [Fintype M] (S : Submodule R M) : Fintype (M ⧸ S) :=
  @_root_.Quotient.fintype _ _ _ fun _ _ => Classical.dec _

section

variable {M₂ : Type*} [AddCommGroup M₂] [Module R M₂]

/-
**Submodule.strictMono_comap_prod_map** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：strictMono_comap_prod_map : StrictMono fun m : Submodule R M => (m.comap p
.subtype, m.map p.mkQ)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuotientAddGroup.strictMono_comap_prod_map`：∀ {G : Type u} [inst : AddGr
oup G] (N : AddSubgroup G) [nN : N.Normal],   StrictMono fun H => (AddSubgroup.c
omap N.subtype H, AddSubgroup.ma…
· 使用定理 `AddSubgroup.normal_of_isAddCommutative`：∀ {G : Type u_1} [inst : AddGrou
p G] [IsAddCommutative G] (H : AddSubgroup G), H.Normal
· 使用定理 `AddCommMagma.to_isCommutative`：∀ {G : Type u_1} [inst : AddCommMagma G],
 IsAddCommutative G
-/
theorem strictMono_comap_prod_map :
    StrictMono fun m : Submodule R M ↦ (m.comap p.subtype, m.map p.mkQ) :=
  fun m₁ m₂ ↦ QuotientAddGroup.strictMono_comap_prod_map
    p.toAddSubgroup (a := m₁.toAddSubgroup) (b := m₂.toAddSubgroup)

end

variable {R₂ M₂ : Type*} [Ring R₂] [AddCommGroup M₂] [Module R₂ M₂] {τ₁₂ : R →+* R₂}

/-- The map from the quotient of `M` by a submodule `p` to `M₂` induced by a linear map `f : M → M₂`
vanishing on `p`, as a linear map. -/
/-
**Submodule.liftQ** 是 Mathlib 中的一个定义，位于命名空间 `Submodule`。
形式化陈述：liftQ (f : M ->ₛₗ[τ₁₂] M₂) (h : p <= ker f) : M ⧸ p ->ₛₗ[τ₁₂] M₂
参数：f : M ->ₛₗ[τ₁₂] M₂；h : p <= ker f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map from the quotient of `M` by a submodule `p` to `M₂` induced by a linear 
map `f : M → M₂`
vanishing on `p`, as a linear map.
-/
def liftQ (f : M →ₛₗ[τ₁₂] M₂) (h : p ≤ ker f) : M ⧸ p →ₛₗ[τ₁₂] M₂ :=
  { QuotientAddGroup.lift p.toAddSubgroup f.toAddMonoidHom h with
    map_smul' := by rintro a ⟨x⟩; exact f.map_smulₛₗ a x }

@[simp]
/-
**Submodule.liftQ_apply** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：liftQ_apply (f : M ->ₛₗ[τ₁₂] M₂) {h} (x : M) : p.liftQ f h (Quotient.mk x)
 = f x
参数：f : M ->ₛₗ[τ₁₂] M₂；x : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem liftQ_apply (f : M →ₛₗ[τ₁₂] M₂) {h} (x : M) : p.liftQ f h (Quotient.mk x) = f x :=
  rfl

@[simp]
/-
**Submodule.liftQ_mkQ** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：liftQ_mkQ (f : M ->ₛₗ[τ₁₂] M₂) (h) : (p.liftQ f h).comp p.mkQ = f
参数：f : M ->ₛₗ[τ₁₂] M₂；h。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
-/
theorem liftQ_mkQ (f : M →ₛₗ[τ₁₂] M₂) (h) : (p.liftQ f h).comp p.mkQ = f := by ext; rfl
/-
**Submodule.pi_liftQ_eq_liftQ_pi** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：pi_liftQ_eq_liftQ_pi {ι : Type*} {N : ι -> Type*} [forall i, AddCommGroup 
(N i)] [forall i, Module R (N i)] (f : (i : ι) -> M ->ₗ[R] (N i)) {p : Submodule
 R M} (h : forall i, p <= ker (f i)) : LinearMap.pi (fun i => p.liftQ (f i) (h i
)) = p.liftQ (LinearMap.pi f) (LinearMap.ker_pi f ▸ le_iInf h)
参数：N i；N i；f : (i : ι) -> M ->ₗ[R] (N i)；h : forall i, p <= ker (f i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.linearMap_qext`：linearMap_qext ⦃f g : M ⧸ p ->ₛₗ[τ₁₂] M₂⦄ (h :
 f.comp p.mkQ = g.comp p.mkQ) : f = g
· 使用定理 `le_iInf`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] {f :
 ι → α} {a : α}, (∀ (i : ι), a ≤ f i) → a ≤ iInf f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.ker_pi`：ker_pi (f : (i : ι) -> M₂ ->ₗ[R] φ i) : ker (pi f) = ⨅
 i : ι, ker (f i)
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Submodule.liftQ_mkQ`：liftQ_mkQ (f : M ->ₛₗ[τ₁₂] M₂) (h) : (p.liftQ f h).
comp p.mkQ = f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem pi_liftQ_eq_liftQ_pi {ι : Type*} {N : ι → Type*}
    [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)]
    (f : (i : ι) → M →ₗ[R] (N i)) {p : Submodule R M} (h : ∀ i, p ≤ ker (f i)) :
    LinearMap.pi (fun i ↦ p.liftQ (f i) (h i)) =
      p.liftQ (LinearMap.pi f) (LinearMap.ker_pi f ▸ le_iInf h) := by
  ext x i
  simp

/-- Special case of `submodule.liftQ` when `p` is the span of `x`. In this case, the condition on
`f` simply becomes vanishing at `x`. -/
/-
**Submodule.liftQSpanSingleton** 是 Mathlib 中的一个定义，位于命名空间 `Submodule`。
形式化陈述：liftQSpanSingleton (x : M) (f : M ->ₛₗ[τ₁₂] M₂) (h : f x = 0) : (M ⧸ R ∙ x
) ->ₛₗ[τ₁₂] M₂
参数：x : M；f : M ->ₛₗ[τ₁₂] M₂；h : f x = 0。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Special case of `submodule.liftQ` when `p` is the span of `x`. In this case, the
 condition on
`f` simply becomes vanishing at `x`.
-/
def liftQSpanSingleton (x : M) (f : M →ₛₗ[τ₁₂] M₂) (h : f x = 0) : (M ⧸ R ∙ x) →ₛₗ[τ₁₂] M₂ :=
  (R ∙ x).liftQ f <| by rw [span_singleton_le_iff_mem, LinearMap.mem_ker, h]

@[simp]
/-
**Submodule.liftQSpanSingleton_apply** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：liftQSpanSingleton_apply (x : M) (f : M ->ₛₗ[τ₁₂] M₂) (h : f x = 0) (y : M
) : liftQSpanSingleton x f h (Quotient.mk y) = f y
参数：x : M；f : M ->ₛₗ[τ₁₂] M₂；h : f x = 0；y : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem liftQSpanSingleton_apply (x : M) (f : M →ₛₗ[τ₁₂] M₂) (h : f x = 0) (y : M) :
    liftQSpanSingleton x f h (Quotient.mk y) = f y :=
  rfl

@[simp]
/-
**Submodule.range_mkQ** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：range_mkQ : range p.mkQ = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.eq_top_iff'`：eq_top_iff' {p : Submodule R M} : p = ⊤ ↔ forall 
x, x in p
-/
theorem range_mkQ : range p.mkQ = ⊤ :=
  eq_top_iff'.2 <| by rintro ⟨x⟩; exact ⟨x, rfl⟩

@[simp]
/-
**Submodule.ker_mkQ** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：ker_mkQ : ker p.mkQ = p
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem ker_mkQ : ker p.mkQ = p := by ext; simp
/-
**Submodule.le_comap_mkQ** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：le_comap_mkQ (p' : Submodule R (M ⧸ p)) : p <= comap p.mkQ p'
参数：p' : Submodule R (M ⧸ p)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.ker_mkQ`：ker_mkQ : ker p.mkQ = p
· 使用定理 `Submodule.comap_mono`：comap_mono {f : M ->ₛₗ[σ₁₂] M₂} {q q' : Submodule 
R₂ M₂} : q <= q' -> comap f q <= comap f q'
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
-/
theorem le_comap_mkQ (p' : Submodule R (M ⧸ p)) : p ≤ comap p.mkQ p' := by
  simpa using (comap_mono bot_le : ker p.mkQ ≤ comap p.mkQ p')

@[simp]
/-
**Submodule.mkQ_map_self** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：mkQ_map_self : map p.mkQ p = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a = ⊥ ↔ a ≤ ⊥
· 使用定理 `Submodule.map_le_iff_le_comap`：map_le_iff_le_comap {f : M ->ₛₗ[σ₁₂] M₂} 
{p : Submodule R M} {q : Submodule R₂ M₂} : map f p <= q ↔ p <= comap f q
· 使用定理 `Submodule.comap_bot`：comap_bot (f : M ->ₛₗ[τ₁₂] M₂) : comap f ⊥ = ker f
· 使用定理 `Submodule.ker_mkQ`：ker_mkQ : ker p.mkQ = p
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem mkQ_map_self : map p.mkQ p = ⊥ := by
  rw [eq_bot_iff, map_le_iff_le_comap, comap_bot, ker_mkQ]

@[simp]
/-
**Submodule.comap_map_mkQ** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：comap_map_mkQ : comap p.mkQ (map p.mkQ p') = p ⊔ p'
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.comap_map_eq`：comap_map_eq (f : M ->ₛₗ[τ₁₂] M₂) (p : Submodule
 R M) : comap f (map f p) = p ⊔ LinearMap.ker f
· 使用定理 `Submodule.ker_mkQ`：ker_mkQ : ker p.mkQ = p
· 使用定理 `sup_comm`：sup_comm (a b : α) : a ⊔ b = b ⊔ a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem comap_map_mkQ : comap p.mkQ (map p.mkQ p') = p ⊔ p' := by simp [comap_map_eq, sup_comm]

@[simp]
/-
**Submodule.map_mkQ_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：map_mkQ_eq_top : map p.mkQ p' = ⊤ ↔ p ⊔ p' = ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.map_eq_top_iff`：map_eq_top_iff {f : M ->ₛₗ[τ₁₂] M₂} (hf : rang
e f = ⊤) {p : Submodule R M} : p.map f = ⊤ ↔ p ⊔ LinearMap.ker f = ⊤
· 使用定理 `Submodule.range_mkQ`：range_mkQ : range p.mkQ = ⊤
· 使用定理 `Submodule.ker_mkQ`：ker_mkQ : ker p.mkQ = p
· 使用定理 `sup_comm`：sup_comm (a b : α) : a ⊔ b = b ⊔ a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem map_mkQ_eq_top : map p.mkQ p' = ⊤ ↔ p ⊔ p' = ⊤ := by
  simp only [LinearMap.map_eq_top_iff p.range_mkQ, sup_comm, ker_mkQ]

variable (q : Submodule R₂ M₂)

/-- The map from the quotient of `M` by submodule `p` to the quotient of `M₂` by submodule `q` along
`f : M → M₂` is linear. -/
/-
**Submodule.mapQ** 是 Mathlib 中的一个定义，位于命名空间 `Submodule`。
形式化陈述：mapQ (f : M ->ₛₗ[τ₁₂] M₂) (h : p <= comap f q) : M ⧸ p ->ₛₗ[τ₁₂] M₂ ⧸ q
参数：f : M ->ₛₗ[τ₁₂] M₂；h : p <= comap f q。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map from the quotient of `M` by submodule `p` to the quotient of `M₂` by sub
module `q` along
`f : M → M₂` is linear.
-/
def mapQ (f : M →ₛₗ[τ₁₂] M₂) (h : p ≤ comap f q) : M ⧸ p →ₛₗ[τ₁₂] M₂ ⧸ q :=
  p.liftQ (q.mkQ.comp f) <| by simpa [ker_comp] using h

@[simp]
/-
**Submodule.mapQ_apply** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：mapQ_apply (f : M ->ₛₗ[τ₁₂] M₂) {h} (x : M) : mapQ p q f h (Quotient.mk x)
 = Quotient.mk (f x)
参数：f : M ->ₛₗ[τ₁₂] M₂；x : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mapQ_apply (f : M →ₛₗ[τ₁₂] M₂) {h} (x : M) :
    mapQ p q f h (Quotient.mk x) = Quotient.mk (f x) :=
  rfl
/-
**Submodule.mapQ_mkQ** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：mapQ_mkQ (f : M ->ₛₗ[τ₁₂] M₂) {h} : (mapQ p q f h).comp p.mkQ = q.mkQ.comp
 f
参数：f : M ->ₛₗ[τ₁₂] M₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
-/
theorem mapQ_mkQ (f : M →ₛₗ[τ₁₂] M₂) {h} : (mapQ p q f h).comp p.mkQ = q.mkQ.comp f := by
  ext x; rfl

@[simp]
/-
**Submodule.mapQ_zero** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：mapQ_zero (h : p <= q.comap (0 : M ->ₛₗ[τ₁₂] M₂)
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.linearMap_qext`：linearMap_qext ⦃f g : M ⧸ p ->ₛₗ[τ₁₂] M₂⦄ (h :
 f.comp p.mkQ = g.comp p.mkQ) : f = g
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mapQ_zero (h : p ≤ q.comap (0 : M →ₛₗ[τ₁₂] M₂) := (by simp)) :
    p.mapQ q (0 : M →ₛₗ[τ₁₂] M₂) h = 0 := by
  ext
  simp

set_option backward.isDefEq.respectTransparency false in
/-- Given submodules `p ⊆ M`, `p₂ ⊆ M₂`, `p₃ ⊆ M₃` and maps `f : M → M₂`, `g : M₂ → M₃` inducing
`mapQ f : M ⧸ p → M₂ ⧸ p₂` and `mapQ g : M₂ ⧸ p₂ → M₃ ⧸ p₃` then
`mapQ (g ∘ f) = (mapQ g) ∘ (mapQ f)`. -/
/-
**Submodule.mapQ_comp** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：mapQ_comp {R₃ M₃ : Type*} [Ring R₃] [AddCommGroup M₃] [Module R₃ M₃] (p₂ :
 Submodule R₂ M₂) (p₃ : Submodule R₃ M₃) {τ₂₃ : R₂ ->+* R₃} {τ₁₃ : R ->+* R₃} [R
ingHomCompTriple τ₁₂ τ₂₃ τ₁₃] (f : M ->ₛₗ[τ₁₂] M₂) (g : M₂ ->ₛₗ[τ₂₃] M₃) (hf : p
 <= p₂.comap f) (hg : p₂ <= p₃.comap g) (h
参数：p₂ : Submodule R₂ M₂；p₃ : Submodule R₃ M₃；f : M ->ₛₗ[τ₁₂] M₂；g : M₂ ->ₛₗ[τ₂₃]
 M₃；hf : p <= p₂.comap f；hg : p₂ <= p₃.comap g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.linearMap_qext`：linearMap_qext ⦃f g : M ⧸ p ->ₛₗ[τ₁₂] M₂⦄ (h :
 f.comp p.mkQ = g.comp p.mkQ) : f = g
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Given submodules `p ⊆ M`, `p₂ ⊆ M₂`, `p₃ ⊆ M₃` and maps `f : M → M₂`, `g : M₂ → 
M₃` inducing
`mapQ f : M ⧸ p → M₂ ⧸ p₂` and `mapQ g : M₂ ⧸ p₂ → M₃ ⧸ p₃` then
`mapQ (g ∘ f) = (mapQ g) ∘ (mapQ f)`.
-/
theorem mapQ_comp {R₃ M₃ : Type*} [Ring R₃] [AddCommGroup M₃] [Module R₃ M₃] (p₂ : Submodule R₂ M₂)
    (p₃ : Submodule R₃ M₃) {τ₂₃ : R₂ →+* R₃} {τ₁₃ : R →+* R₃} [RingHomCompTriple τ₁₂ τ₂₃ τ₁₃]
    (f : M →ₛₗ[τ₁₂] M₂) (g : M₂ →ₛₗ[τ₂₃] M₃) (hf : p ≤ p₂.comap f) (hg : p₂ ≤ p₃.comap g)
    (h := hf.trans (comap_mono hg)) :
    p.mapQ p₃ (g.comp f) h = (p₂.mapQ p₃ g hg).comp (p.mapQ p₂ f hf) := by
  ext
  simp

@[simp]
/-
**Submodule.mapQ_id** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：mapQ_id (h : p <= p.comap LinearMap.id
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.linearMap_qext`：linearMap_qext ⦃f g : M ⧸ p ->ₛₗ[τ₁₂] M₂⦄ (h :
 f.comp p.mkQ = g.comp p.mkQ) : f = g
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mapQ_id (h : p ≤ p.comap LinearMap.id := (by rw [comap_id])) :
    p.mapQ p LinearMap.id h = LinearMap.id := by
  ext
  simp
/-
**Submodule.mapQ_pow** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：mapQ_pow {f : M ->ₗ[R] M} (h : p <= p.comap f) (k : Nat) (h' : p <= p.coma
p (f ^ k)
参数：h : p <= p.comap f；k : Nat。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Submodule.mapQ.congr_simp`：∀ {R : Type u_1} {M : Type u_2} [inst : Ring 
R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   (p : Submodule R M) 
{R₂ : Type u_3}…
· 使用定理 `Submodule.mapQ_id`：mapQ_id (h : p <= p.comap LinearMap.id
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Module.End.iterate_succ`：iterate_succ (n : Nat) : f' ^ (n + 1) = .comp (
f' ^ n) f'
· 使用定理 `Submodule.le_comap_pow_of_le_comap`：le_comap_pow_of_le_comap (p : Submod
ule R M) {f : M ->ₗ[R] M} (h : p <= p.comap f) (k : Nat) : p <= p.comap (f ^ k)
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Submodule.comap_mono`：comap_mono {f : M ->ₛₗ[σ₁₂] M₂} {q q' : Submodule 
R₂ M₂} : q <= q' -> comap f q <= comap f q'
· 使用定理 `Submodule.mapQ_comp`：mapQ_comp {R₃ M₃ : Type*} [Ring R₃] [AddCommGroup M
₃] [Module R₃ M₃] (p₂ : Submodule R₂ M₂) (p₃ : Submodule R₃ M₃) {τ₂₃ : R₂ ->+* R
₃} {τ₁₃ :…
-/
theorem mapQ_pow {f : M →ₗ[R] M} (h : p ≤ p.comap f) (k : ℕ)
    (h' : p ≤ p.comap (f ^ k) := p.le_comap_pow_of_le_comap h k) :
    p.mapQ p (f ^ k) h' = p.mapQ p f h ^ k := by
  induction k with
  | zero => simp [Module.End.one_eq_id]
  | succ k ih =>
    simp only [Module.End.iterate_succ]
    rw [mapQ_comp, ih]
    exact p.le_comap_pow_of_le_comap h k
/-
**Submodule.comap_liftQ** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：comap_liftQ (f : M ->ₛₗ[τ₁₂] M₂) (h) : q.comap (p.liftQ f h) = (q.comap f)
.map (mkQ p)
参数：f : M ->ₛₗ[τ₁₂] M₂；h。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.map_le_iff_le_comap`：map_le_iff_le_comap {f : M ->ₛₗ[σ₁₂] M₂} 
{p : Submodule R M} {q : Submodule R₂ M₂} : map f p <= q ↔ p <= comap f q
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.comap_comp`：comap_comp (f : M ->ₛₗ[σ₁₂] M₂) (g : M₂ ->ₛₗ[σ₂₃] 
M₃) (p : Submodule R₃ M₃) : comap (g.comp f : M ->ₛₗ[σ₁₃] M₃) p = comap f (comap
 g p)
· 使用定理 `Submodule.liftQ_mkQ`：liftQ_mkQ (f : M ->ₛₗ[τ₁₂] M₂) (h) : (p.liftQ f h).
comp p.mkQ = f
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem comap_liftQ (f : M →ₛₗ[τ₁₂] M₂) (h) : q.comap (p.liftQ f h) = (q.comap f).map (mkQ p) :=
  le_antisymm (by rintro ⟨x⟩ hx; exact ⟨_, hx, rfl⟩)
    (by rw [map_le_iff_le_comap, ← comap_comp, liftQ_mkQ])
/-
**Submodule.map_liftQ** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：map_liftQ [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] M₂) (h) (q : Submodule 
R (M ⧸ p)) : q.map (p.liftQ f h) = (q.comap p.mkQ).map f
参数：f : M ->ₛₗ[τ₁₂] M₂；h；q : Submodule R (M ⧸ p)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
-/
theorem map_liftQ [RingHomSurjective τ₁₂] (f : M →ₛₗ[τ₁₂] M₂) (h) (q : Submodule R (M ⧸ p)) :
    q.map (p.liftQ f h) = (q.comap p.mkQ).map f :=
  le_antisymm (by rintro _ ⟨⟨x⟩, hxq, rfl⟩; exact ⟨x, hxq, rfl⟩)
    (by rintro _ ⟨x, hxq, rfl⟩; exact ⟨Quotient.mk x, hxq, rfl⟩)
/-
**Submodule.ker_liftQ** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：ker_liftQ (f : M ->ₛₗ[τ₁₂] M₂) (h) : ker (p.liftQ f h) = (ker f).map (mkQ 
p)
参数：f : M ->ₛₗ[τ₁₂] M₂；h。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.comap_liftQ`：comap_liftQ (f : M ->ₛₗ[τ₁₂] M₂) (h) : q.comap (p
.liftQ f h) = (q.comap f).map (mkQ p)
-/
theorem ker_liftQ (f : M →ₛₗ[τ₁₂] M₂) (h) : ker (p.liftQ f h) = (ker f).map (mkQ p) :=
  comap_liftQ _ _ _ _
/-
**Submodule.ker_mapQ** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：ker_mapQ (f : M ->ₛₗ[τ₁₂] M₂) (h) : ker (p.mapQ q f h) = (comap f q).map p
.mkQ
参数：f : M ->ₛₗ[τ₁₂] M₂；h。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.ker_liftQ`：ker_liftQ (f : M ->ₛₗ[τ₁₂] M₂) (h) : ker (p.liftQ f
 h) = (ker f).map (mkQ p)
· 使用定理 `Submodule.map.congr_simp`：∀ {R : Type u_1} {R₂ : Type u_3} {M : Type u_5
} {M₂ : Type u_7} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : AddComm
Monoid M] [ins…
· 使用定理 `Submodule.ker_mkQ`：ker_mkQ : ker p.mkQ = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma ker_mapQ (f : M →ₛₗ[τ₁₂] M₂) (h) : ker (p.mapQ q f h) = (comap f q).map p.mkQ := by
  simp [Submodule.mapQ, Submodule.ker_liftQ, LinearMap.ker_comp]
/-
**Submodule.range_liftQ** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：range_liftQ [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] M₂) (h) : range (p.li
ftQ f h) = range f
参数：f : M ->ₛₗ[τ₁₂] M₂；h。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.range_eq_map`：range_eq_map [RingHomSurjective τ₁₂] (f : M ->ₛₗ
[τ₁₂] M₂) : range f = map f ⊤
· 使用定理 `Submodule.map_liftQ`：map_liftQ [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] 
M₂) (h) (q : Submodule R (M ⧸ p)) : q.map (p.liftQ f h) = (q.comap p.mkQ).map f
-/
theorem range_liftQ [RingHomSurjective τ₁₂] (f : M →ₛₗ[τ₁₂] M₂) (h) :
    range (p.liftQ f h) = range f := by simpa only [range_eq_map] using! map_liftQ _ _ _ _
/-
**Submodule.ker_liftQ_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：ker_liftQ_eq_bot (f : M ->ₛₗ[τ₁₂] M₂) (h) (h' : ker f <= p) : ker (p.liftQ
 f h) = ⊥
参数：f : M ->ₛₗ[τ₁₂] M₂；h；h' : ker f <= p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.ker_liftQ`：ker_liftQ (f : M ->ₛₗ[τ₁₂] M₂) (h) : ker (p.liftQ f
 h) = (ker f).map (mkQ p)
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Submodule.mkQ_map_self`：mkQ_map_self : map p.mkQ p = ⊥
-/
theorem ker_liftQ_eq_bot (f : M →ₛₗ[τ₁₂] M₂) (h) (h' : ker f ≤ p) : ker (p.liftQ f h) = ⊥ := by
  rw [ker_liftQ, le_antisymm h h', mkQ_map_self]
/-
**Submodule.ker_liftQ_eq_bot'** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：ker_liftQ_eq_bot' (f : M ->ₛₗ[τ₁₂] M₂) (h : p = ker f) : ker (p.liftQ f (l
e_of_eq h)) = ⊥
参数：f : M ->ₛₗ[τ₁₂] M₂；h : p = ker f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.ker_liftQ_eq_bot`：ker_liftQ_eq_bot (f : M ->ₛₗ[τ₁₂] M₂) (h) (h
' : ker f <= p) : ker (p.liftQ f h) = ⊥
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
-/
theorem ker_liftQ_eq_bot' (f : M →ₛₗ[τ₁₂] M₂) (h : p = ker f) :
    ker (p.liftQ f (le_of_eq h)) = ⊥ :=
  ker_liftQ_eq_bot p f h.le h.ge
/-
**Submodule.range_mapQ** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：range_mapQ [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] M₂) (h : p <= comap f 
q) : (p.mapQ q f h).range = f.range.map q.mkQ
参数：f : M ->ₛₗ[τ₁₂] M₂；h : p <= comap f q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.mapQ.eq_1`：∀ {R : Type u_1} {M : Type u_2} [inst : Ring R] [in
st_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   (p : Submodule R M) {R₂ : 
Type u_3}…
· 使用定理 `Submodule.range_liftQ`：range_liftQ [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ
₁₂] M₂) (h) : range (p.liftQ f h) = range f
· 使用定理 `LinearMap.range_comp`：range_comp [RingHomSurjective τ₁₂] [RingHomSurject
ive τ₂₃] [RingHomSurjective τ₁₃] (f : M ->ₛₗ[τ₁₂] M₂) (g : M₂ ->ₛₗ[τ₂₃] M₃) : ra
nge (g.com…
-/
theorem range_mapQ [RingHomSurjective τ₁₂] (f : M →ₛₗ[τ₁₂] M₂) (h : p ≤ comap f q) :
    (p.mapQ q f h).range = f.range.map q.mkQ := by
  rw [mapQ, range_liftQ, range_comp]

section

variable {p p' p''}

/-- The linear map from the quotient by a smaller submodule to the quotient by a larger submodule.

This is the `Submodule.Quotient` version of `Quot.Factor`

When the two submodules are of the form `I ^ m • ⊤` and `I ^ n • ⊤` and `n ≤ m`,
please refer to the dedicated version `Submodule.factorPow`. -/
/-
**Submodule.factor** 是 Mathlib 中的一个缩写定义，位于命名空间 `Submodule`。
形式化陈述：factor (H : p <= p') : M ⧸ p ->ₗ[R] M ⧸ p'
参数：H : p <= p'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The linear map from the quotient by a smaller submodule to the quotient by a lar
ger submodule.

This is the `Submodule.Quotient` version of `Quot.Factor`

When the two submodules are of the form `I ^ m • ⊤` and `I ^ n • ⊤` and `n ≤ m`,
please refer to the dedicated version `Submodule.factorPow`.
-/
abbrev factor (H : p ≤ p') : M ⧸ p →ₗ[R] M ⧸ p' :=
  mapQ _ _ LinearMap.id H

@[simp]
/-
**Submodule.factor_mk** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：factor_mk (H : p <= p') (x : M) : factor H (mkQ p x) = mkQ p' x
参数：H : p <= p'；x : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem factor_mk (H : p ≤ p') (x : M) : factor H (mkQ p x) = mkQ p' x :=
  rfl

@[simp]
/-
**Submodule.factor_comp_mk** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：factor_comp_mk (H : p <= p') : (factor H).comp (mkQ p) = mkQ p'
参数：H : p <= p'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.comp_apply`：comp_apply (x : M₁) : f.comp g x = f (g x)
· 使用定理 `Submodule.factor_mk`：factor_mk (H : p <= p') (x : M) : factor H (mkQ p x
) = mkQ p' x
-/
theorem factor_comp_mk (H : p ≤ p') : (factor H).comp (mkQ p) = mkQ p' := by
  ext x
  rw [LinearMap.comp_apply, factor_mk]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**Submodule.factor_comp** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：factor_comp (H1 : p <= p') (H2 : p' <= p'') : (factor H2).comp (factor H1)
 = factor (H1.trans H2)
参数：H1 : p <= p'；H2 : p' <= p''。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.linearMap_qext`：linearMap_qext ⦃f g : M ⧸ p ->ₛₗ[τ₁₂] M₂⦄ (h :
 f.comp p.mkQ = g.comp p.mkQ) : f = g
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Submodule.factor_comp_mk`：factor_comp_mk (H : p <= p') : (factor H).comp
 (mkQ p) = mkQ p'
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem factor_comp (H1 : p ≤ p') (H2 : p' ≤ p'') :
    (factor H2).comp (factor H1) = factor (H1.trans H2) := by
  ext
  simp

@[simp]
/-
**Submodule.factor_comp_apply** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：factor_comp_apply (H1 : p <= p') (H2 : p' <= p'') (x : M ⧸ p) : factor H2 
(factor H1 x) = factor (H1.trans H2) x
参数：H1 : p <= p'；H2 : p' <= p''；x : M ⧸ p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.comp_apply`：comp_apply (x : M₁) : f.comp g x = f (g x)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Submodule.factor_comp`：factor_comp (H1 : p <= p') (H2 : p' <= p'') : (fa
ctor H2).comp (factor H1) = factor (H1.trans H2)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem factor_comp_apply (H1 : p ≤ p') (H2 : p' ≤ p'') (x : M ⧸ p) :
    factor H2 (factor H1 x) = factor (H1.trans H2) x := by
  rw [← comp_apply]
  simp
/-
**Submodule.factor_surjective** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：factor_surjective (H : p <= p') : Function.Surjective (factor H)
参数：H : p <= p'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.out_eq`：Quotient.out_eq {s : Setoid α} (q : Quotient s) : ⟦q.ou
t⟧ = q
-/
lemma factor_surjective (H : p ≤ p') : Function.Surjective (factor H) := by
  intro x
  use Quotient.mk x.out
  exact Quotient.out_eq x

end

/-- The correspondence theorem for modules: there is an order isomorphism between submodules of the
quotient of `M` by `p`, and submodules of `M` larger than `p`. -/
/-
**Submodule.comapMkQRelIso** 是 Mathlib 中的一个定义，位于命名空间 `Submodule`。
形式化陈述：comapMkQRelIso : Submodule R (M ⧸ p) ≃o Set.Ici p where toFun p'
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.le_comap_mkQ`：le_comap_mkQ (p' : Submodule R (M ⧸ p)) : p <= c
omap p.mkQ p'

--- 原说明 ---
The correspondence theorem for modules: there is an order isomorphism between su
bmodules of the
quotient of `M` by `p`, and submodules of `M` larger than `p`.
-/
def comapMkQRelIso : Submodule R (M ⧸ p) ≃o Set.Ici p where
  toFun p' := ⟨comap p.mkQ p', le_comap_mkQ p _⟩
  invFun q := map p.mkQ q
  left_inv p' := map_comap_eq_self <| by simp
  right_inv := fun ⟨q, hq⟩ => Subtype.ext <| by simpa [comap_map_mkQ p]
  map_rel_iff' := comap_le_comap_iff <| range_mkQ _

/-- The ordering on submodules of the quotient of `M` by `p` embeds into the ordering on submodules
of `M`. -/
/-
**Submodule.comapMkQOrderEmbedding** 是 Mathlib 中的一个定义，位于命名空间 `Submodule`。
形式化陈述：comapMkQOrderEmbedding : Submodule R (M ⧸ p) ↪o Submodule R M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The ordering on submodules of the quotient of `M` by `p` embeds into the orderin
g on submodules
of `M`.
-/
def comapMkQOrderEmbedding : Submodule R (M ⧸ p) ↪o Submodule R M :=
  (RelIso.toRelEmbedding <| comapMkQRelIso p).trans (Subtype.relEmbedding (· ≤ ·) _)

@[simp]
/-
**Submodule.comapMkQOrderEmbedding_eq** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：comapMkQOrderEmbedding_eq (p' : Submodule R (M ⧸ p)) : comapMkQOrderEmbedd
ing p p' = comap p.mkQ p'
参数：p' : Submodule R (M ⧸ p)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comapMkQOrderEmbedding_eq (p' : Submodule R (M ⧸ p)) :
    comapMkQOrderEmbedding p p' = comap p.mkQ p' :=
  rfl
/-
**Submodule.span_preimage_eq** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：span_preimage_eq [RingHomSurjective τ₁₂] {f : M ->ₛₗ[τ₁₂] M₂} {s : Set M₂}
 (h₀ : s.Nonempty) (h₁ : s subseteq range f) : span R (f ⁻¹' s) = (span R₂ s).co
map f
参数：h₀ : s.Nonempty；h₁ : s subseteq range f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.ker_le_iff`：ker_le_iff [RingHomSurjective τ₁₂] {p : Submodule 
R M} : ker f <= p ↔ exists y in range f, f ⁻¹' {y} subseteq p
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s
· 使用定理 `Submodule.span_mono`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R]
 [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {s t : Set M}, s ⊆ t 
→ Submodu…
· 使用定理 `Set.preimage_mono`：preimage_mono {s t : Set β} (h : s subseteq t) : f ⁻¹
' s subseteq f ⁻¹' t
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.singleton_subset_iff`：singleton_subset_iff {a : α} {s : Set α} : {a}
 subseteq s ↔ a in s
· 使用定理 `left_eq_sup`：left_eq_sup : a = a ⊔ b ↔ b <= a
· 使用定理 `LinearMap.map_le_map_iff`：∀ {R : Type u_1} {R₂ : Type u_2} {M : Type u_4
} {M₂ : Type u_5} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : AddComm
Group M] [inst…
· 使用定理 `Submodule.map_span`：map_span [RingHomSurjective σ₁₂] (f : M ->ₛₗ[σ₁₂] M₂
) (s : Set M) : (span R s).map f = span R₂ (f '' s)
· 使用定理 `Submodule.map_comap_eq`：∀ {R : Type u_1} {R₂ : Type u_2} {M : Type u_5} 
{M₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : AddCommMo
noid M] [ins…
· 使用定理 `Set.image_preimage_eq_of_subset`：image_preimage_eq_of_subset {f : α -> β
} {s : Set β} (hs : s subseteq range f) : f '' f ⁻¹' s = s
· 使用定理 `LinearMap.coe_range`：coe_range [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] 
M₂) : (range f : Set M₂) = Set.range f
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Submodule.span_preimage_le`：span_preimage_le (f : M ->ₛₗ[σ₁₂] M₂) (s : S
et M₂) : span R (f ⁻¹' s) <= (span R₂ s).comap f
-/
theorem span_preimage_eq [RingHomSurjective τ₁₂] {f : M →ₛₗ[τ₁₂] M₂} {s : Set M₂} (h₀ : s.Nonempty)
    (h₁ : s ⊆ range f) : span R (f ⁻¹' s) = (span R₂ s).comap f := by
  suffices (span R₂ s).comap f ≤ span R (f ⁻¹' s) by exact le_antisymm (span_preimage_le f s) this
  have hk : ker f ≤ span R (f ⁻¹' s) := by
    let y := Classical.choose h₀
    have hy : y ∈ s := Classical.choose_spec h₀
    rw [ker_le_iff]
    use y, h₁ hy
    rw [← Set.singleton_subset_iff] at hy
    exact Set.Subset.trans subset_span (span_mono (Set.preimage_mono hy))
  rw [← left_eq_sup] at hk
  rw [coe_range f] at h₁
  rw [hk, ← LinearMap.map_le_map_iff, map_span, map_comap_eq, Set.image_preimage_eq_of_subset h₁]
  exact inf_le_right

variable {R₂ : Type*} [Ring R₂] {σ₁₂ : R →+* R₂} {σ₂₁ : R₂ →+* R}
  [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂]
variable {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R₂ N]
  (P : Submodule R M) (Q : Submodule R₂ N)

/-- If `P` is a submodule of `M` and `Q` a submodule of `N`,
and `f : M ≃ₛₗ[σ] N` maps `P` to `Q`, then `M ⧸ P` is equivalent to `N ⧸ Q`. -/
/-
**Submodule.Quotient.equiv** 是 Mathlib 中的一个定义，位于命名空间 `Submodule.Quotient`。
形式化陈述：{R : Type u_1} →   [inst : Ring R] →     {R₂ : Type u_5} →       [inst_1 :
 Ring R₂] →         {σ₁₂ : R →+* R₂} →           {σ₂₁ : R₂ →+* R} →             
[inst_2 : RingHomInvPair σ₁₂ σ₂₁] →               [inst_3 : RingHomInvPair σ₂₁ σ
₁₂] →                 {M : Type u_6} →                   {N : Type u_7} →       
              [inst_4 : AddCommGroup M] →                       [inst_5 : _root_
.Module R M] →                         [inst_6 : AddCommGroup N] →              
             [inst_7 : _root_.Module R₂ N] →                             (P : Su
bmodule R M) →                               (Q : Submodule R₂ N) →             
                    (f : M ≃ₛₗ[σ₁₂] N) → Submodule.map (↑f) P = Q → (M ⧸ P) ≃ₛₗ[
σ₁₂] N ⧸ Q
参数：P : Submodule R M；Q : Submodule R₂ N；f : M ≃ₛₗ[σ₁₂] N；↑f；M ⧸ P。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `P` is a submodule of `M` and `Q` a submodule of `N`,
and `f : M ≃ₛₗ[σ] N` maps `P` to `Q`, then `M ⧸ P` is equivalent to `N ⧸ Q`.
-/
def Quotient.equiv (f : M ≃ₛₗ[σ₁₂] N) (hf : P.map (f : M →ₛₗ[σ₁₂] N) = Q) :
    (M ⧸ P) ≃ₛₗ[σ₁₂] N ⧸ Q where
  __ := P.mapQ Q (f : M →ₛₗ[σ₁₂] N) (map_le_iff_le_comap.mp hf.le)
  invFun := Q.mapQ P (f.symm : N →ₛₗ[σ₂₁] M) (hf.symm.trans (map_equiv_eq_comap_symm f _)).le
  left_inv x := Quotient.induction_on _ x (by simp)
  right_inv x := Quotient.induction_on _ x (by simp)

@[simp]
/-
**Submodule.Quotient.equiv_apply** 是 Mathlib 中的一个定理，位于命名空间 `Submodule.Quotient`。
形式化陈述：∀ {R : Type u_1} [inst : Ring R] {R₂ : Type u_5} [inst_1 : Ring R₂] {σ₁₂ :
 R →+* R₂} {σ₂₁ : R₂ →+* R}   [inst_2 : RingHomInvPair σ₁₂ σ₂₁] [inst_3 : RingHo
mInvPair σ₂₁ σ₁₂] {M : Type u_6} {N : Type u_7}   [inst_4 : AddCommGroup M] [ins
t_5 : _root_.Module R M] [inst_6 : AddCommGroup N] [inst_7 : _root_.Module R₂ N]
   (P : Submodule R M) (Q : Submodule R₂ N) (f : M ≃ₛₗ[σ₁₂] N) (hf : Submodule.m
ap (↑f) P = Q) (a : M ⧸ P),   (Submodule.Quotient.equiv P Q f hf) a = (P.mapQ Q 
↑f ⋯) a
参数：P : Submodule R M；Q : Submodule R₂ N；f : M ≃ₛₗ[σ₁₂] N；hf : Submodule.map (↑f)
 P = Q；a : M ⧸ P；Submodule.Quotient.equiv P Q f hf；P.mapQ Q ↑f ⋯。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHomSurjective.invPair`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : Sem
iring R₁] [inst_1 : Semiring R₂] {σ₁ : R₁ →+* R₂} {σ₂ : R₂ →+* R₁}   [RingHomInv
Pair σ₁ σ₂], Ri…
-/
lemma Quotient.equiv_apply (f : M ≃ₛₗ[σ₁₂] N) (hf : P.map (f : M →ₛₗ[σ₁₂] N) = Q) (a : M ⧸ P) :
    equiv P Q f hf a = P.mapQ Q (f : M →ₛₗ[σ₁₂] N) (map_le_iff_le_comap.mp hf.le) a :=
  rfl

@[simp]
/-
**Submodule.Quotient.equiv_symm** 是 Mathlib 中的一个定理，位于命名空间 `Submodule.Quotient`。
形式化陈述：∀ {R : Type u_1} [inst : Ring R] {R₂ : Type u_5} [inst_1 : Ring R₂] {σ₁₂ :
 R →+* R₂} {σ₂₁ : R₂ →+* R}   [inst_2 : RingHomInvPair σ₁₂ σ₂₁] [inst_3 : RingHo
mInvPair σ₂₁ σ₁₂] {M : Type u_6} {N : Type u_7}   [inst_4 : AddCommGroup M] [ins
t_5 : _root_.Module R M] [inst_6 : AddCommGroup N] [inst_7 : _root_.Module R₂ N]
   (P : Submodule R M) (Q : Submodule R₂ N) (f : M ≃ₛₗ[σ₁₂] N) (hf : Submodule.m
ap (↑f) P = Q),   (Submodule.Quotient.equiv P Q f hf).symm = Submodule.Quotient.
equiv Q P f.symm ⋯
参数：P : Submodule R M；Q : Submodule R₂ N；f : M ≃ₛₗ[σ₁₂] N；hf : Submodule.map (↑f)
 P = Q；Submodule.Quotient.equiv P Q f hf。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHomSurjective.invPair`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : Sem
iring R₁] [inst_1 : Semiring R₂] {σ₁ : R₁ →+* R₂} {σ₂ : R₂ →+* R₁}   [RingHomInv
Pair σ₁ σ₂], Ri…
-/
lemma Quotient.equiv_symm (f : M ≃ₛₗ[σ₁₂] N) (hf : P.map (f : M →ₛₗ[σ₁₂] N) = Q) :
    (Quotient.equiv P Q f hf).symm = Quotient.equiv Q P f.symm ((map_symm_eq_iff f).mpr hf) :=
  rfl

@[simp]
/-
**Submodule.Quotient.equiv_trans** 是 Mathlib 中的一个定理，位于命名空间 `Submodule.Quotient`。
形式化陈述：∀ {R : Type u_1} [inst : Ring R] {R₂ : Type u_5} [inst_1 : Ring R₂] {σ₁₂ :
 R →+* R₂} {σ₂₁ : R₂ →+* R}   [inst_2 : RingHomInvPair σ₁₂ σ₂₁] [inst_3 : RingHo
mInvPair σ₂₁ σ₁₂] {M : Type u_6} {N : Type u_7}   [inst_4 : AddCommGroup M] [ins
t_5 : _root_.Module R M] [inst_6 : AddCommGroup N] [inst_7 : _root_.Module R₂ N]
   (P : Submodule R M) (Q : Submodule R₂ N) {R₃ : Type u_8} {O : Type u_9} [inst
_8 : Ring R₃] [inst_9 : AddCommGroup O]   [inst_10 : _root_.Module R₃ O] {σ₂₃ : 
R₂ →+* R₃} {σ₃₂ : R₃ →+* R₂} {σ₁₃ : R →+* R₃} {σ₃₁ : R₃ →+* R}   [inst_11 : Ring
HomInvPair σ₂₃ σ₃₂] [inst_12 : RingHomInvPair σ₃₂ σ₂₃] [inst_13 : RingHomInvPair
 σ₁₃ σ₃₁]   [inst_14 : RingHomInvPair σ₃₁ σ₁₃] [inst_15 : RingHomCompTriple σ₁₂ 
σ₂₃ σ₁₃] [inst_16 : RingHomCompTriple σ₃₂ σ₂₁ σ₃₁]   (S : Submodule R₃ O) (e : M
 ≃ₛₗ[σ₁₂] N) (f : N ≃ₛₗ[σ₂₃] O) (he : Submodule.map (↑e) P = Q)   (hf : Submodul
e.map (↑f) Q = S) (hef : Submodule.map (↑(e.trans f)) P = S),   Submodule.Quotie
nt.equiv P S (e.trans f) hef =     (Submodule.Quotient.equiv P Q e he).trans (Su
bmodule.Quotient.equiv Q S f hf)
参数：P : Submodule R M；Q : Submodule R₂ N；S : Submodule R₃ O；e : M ≃ₛₗ[σ₁₂] N；f : 
N ≃ₛₗ[σ₂₃] O；he : Submodule.map (↑e) P = Q；hf : Submodule.map (↑f) Q = S；hef : S
ubmodule.map (↑(e.trans f)) P = S；e.trans f；Submodule.Quotient.equiv P Q e he；Su
bmodule.Quotient.equiv Q S f hf。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHomSurjective.invPair`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : Sem
iring R₁] [inst_1 : Semiring R₂] {σ₁ : R₁ →+* R₂} {σ₂ : R₂ →+* R₁}   [RingHomInv
Pair σ₁ σ₂], Ri…
· 使用定理 `LinearEquiv.ext`：ext (h : forall x, e x = e' x) : e = e'
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.map_le_iff_le_comap`：map_le_iff_le_comap {f : M ->ₛₗ[σ₁₂] M₂} 
{p : Submodule R M} {q : Submodule R₂ M₂} : map f p <= q ↔ p <= comap f q
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Submodule.comap_mono`：comap_mono {f : M ->ₛₗ[σ₁₂] M₂} {q q' : Submodule 
R₂ M₂} : q <= q' -> comap f q <= comap f q'
· 使用定理 `Submodule.mapQ_comp`：mapQ_comp {R₃ M₃ : Type*} [Ring R₃] [AddCommGroup M
₃] [Module R₃ M₃] (p₂ : Submodule R₂ M₂) (p₃ : Submodule R₃ M₃) {τ₂₃ : R₂ ->+* R
₃} {τ₁₃ :…
· 使用定理 `LinearMap.comp_apply`：comp_apply (x : M₁) : f.comp g x = f (g x)
-/
theorem Quotient.equiv_trans {R₃ : Type*} {O : Type*} [Ring R₃] [AddCommGroup O] [Module R₃ O]
    {σ₂₃ : R₂ →+* R₃} {σ₃₂ : R₃ →+* R₂} {σ₁₃ : R →+* R₃} {σ₃₁ : R₃ →+* R}
    [RingHomInvPair σ₂₃ σ₃₂] [RingHomInvPair σ₃₂ σ₂₃]
    [RingHomInvPair σ₁₃ σ₃₁] [RingHomInvPair σ₃₁ σ₁₃]
    [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] [RingHomCompTriple σ₃₂ σ₂₁ σ₃₁]
    (S : Submodule R₃ O) (e : M ≃ₛₗ[σ₁₂] N) (f : N ≃ₛₗ[σ₂₃] O)
    (he : P.map (e : M →ₛₗ[σ₁₂] N) = Q) (hf : Q.map (f : N →ₛₗ[σ₂₃] O) = S)
    (hef : P.map ((e.trans f : M ≃ₛₗ[σ₁₃] O) : M →ₛₗ[σ₁₃] O) = S) :
    Quotient.equiv P S (e.trans f) hef =
      (Quotient.equiv P Q e he).trans (Quotient.equiv Q S f hf) := by
  ext
  -- `simp` can deal with `hef` depending on `e` and `f`
  simp only [Quotient.equiv_apply, LinearEquiv.trans_apply, LinearEquiv.coe_trans]
  -- `rw` can deal with `mapQ_comp` needing extra hypotheses coming from the RHS
  rw [mapQ_comp, LinearMap.comp_apply]

end Submodule

open Submodule

namespace LinearMap

section Ring

variable {R M R₂ M₂ R₃ M₃ : Type*}
variable [Ring R] [Ring R₂] [Ring R₃]
variable [AddCommMonoid M] [AddCommGroup M₂] [AddCommMonoid M₃]
variable [Module R M] [Module R₂ M₂] [Module R₃ M₃]
variable {τ₁₂ : R →+* R₂} {τ₂₃ : R₂ →+* R₃} {τ₁₃ : R →+* R₃}
variable [RingHomCompTriple τ₁₂ τ₂₃ τ₁₃] [RingHomSurjective τ₁₂]

/-
**LinearMap.range_mkQ_comp** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：range_mkQ_comp (f : M ->ₛₗ[τ₁₂] M₂) : (range f).mkQ.comp f = 0
参数：f : M ->ₛₗ[τ₁₂] M₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
theorem range_mkQ_comp (f : M →ₛₗ[τ₁₂] M₂) : (range f).mkQ.comp f = 0 :=
  LinearMap.ext fun x => by simp
/-
**LinearMap.ker_le_range_iff** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：ker_le_range_iff {f : M ->ₛₗ[τ₁₂] M₂} {g : M₂ ->ₛₗ[τ₂₃] M₃} : ker g <= ran
ge f ↔ (range f).mkQ.comp (ker g).subtype = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.range_le_ker_iff`：range_le_ker_iff {f : M ->ₛₗ[τ₁₂] M₂} {g : M
₂ ->ₛₗ[τ₂₃] M₃} : range f <= ker g ↔ (g.comp f : M ->ₛₗ[τ₁₃] M₃) = 0
· 使用定理 `Submodule.ker_mkQ`：ker_mkQ : ker p.mkQ = p
· 使用定理 `Submodule.range_subtype`：range_subtype : range p.subtype = p
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem ker_le_range_iff {f : M →ₛₗ[τ₁₂] M₂} {g : M₂ →ₛₗ[τ₂₃] M₃} :
    ker g ≤ range f ↔ (range f).mkQ.comp (ker g).subtype = 0 := by
  rw [← range_le_ker_iff, Submodule.ker_mkQ, Submodule.range_subtype]

/-- An epimorphism is surjective. -/
/-
**LinearMap.range_eq_top_of_cancel** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：range_eq_top_of_cancel {f : M ->ₛₗ[τ₁₂] M₂} (h : forall u v : M₂ ->ₗ[R₂] M
₂ ⧸ (range f), u.comp f = v.comp f -> u = v) : range f = ⊤
参数：h : forall u v : M₂ ->ₗ[R₂] M₂ ⧸ (range f), u.comp f = v.comp f -> u = v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.zero_comp`：zero_comp (f : M ->ₛₗ[σ₁₂] M₂) : ((0 : M₂ ->ₛₗ[σ₂₃]
 M₃).comp f : M ->ₛₗ[σ₁₃] M₃) = 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.ker_mkQ`：ker_mkQ : ker p.mkQ = p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `LinearMap.range_mkQ_comp`：range_mkQ_comp (f : M ->ₛₗ[τ₁₂] M₂) : (range f
).mkQ.comp f = 0
· 使用定理 `LinearMap.ker_zero`：ker_zero : ker (0 : M ->ₛₗ[τ₁₂] M₂) = ⊤

--- 原说明 ---
An epimorphism is surjective.
-/
theorem range_eq_top_of_cancel {f : M →ₛₗ[τ₁₂] M₂}
    (h : ∀ u v : M₂ →ₗ[R₂] M₂ ⧸ (range f), u.comp f = v.comp f → u = v) : range f = ⊤ := by
  have h₁ : (0 : M₂ →ₗ[R₂] M₂ ⧸ (range f)).comp f = 0 := zero_comp _
  rw [← Submodule.ker_mkQ (range f), ← h 0 (range f).mkQ (Eq.trans h₁ (range_mkQ_comp _).symm)]
  exact ker_zero

end Ring

end LinearMap

open LinearMap

namespace Submodule

variable {R M : Type*} {r : R} {x y : M} [Ring R] [AddCommGroup M] [Module R M]
variable (p p' : Submodule R M)

/-- If `p = ⊥`, then `M / p ≃ₗ[R] M`. -/
/-
**Submodule.quotEquivOfEqBot** 是 Mathlib 中的一个定义，位于命名空间 `Submodule`。
形式化陈述：quotEquivOfEqBot (hp : p = ⊥) : (M ⧸ p) ≃ₗ[R] M
参数：hp : p = ⊥。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `p = ⊥`, then `M / p ≃ₗ[R] M`.
-/
def quotEquivOfEqBot (hp : p = ⊥) : (M ⧸ p) ≃ₗ[R] M :=
  LinearEquiv.ofLinearMap (p.liftQ id <| hp.symm ▸ bot_le) p.mkQ (liftQ_mkQ _ _ _) <|
    p.quot_hom_ext _ LinearMap.id fun _ => rfl

@[simp]
/-
**Submodule.quotEquivOfEqBot_apply_mk** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：quotEquivOfEqBot_apply_mk (hp : p = ⊥) (x : M) : p.quotEquivOfEqBot hp (Qu
otient.mk x) = x
参数：hp : p = ⊥；x : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem quotEquivOfEqBot_apply_mk (hp : p = ⊥) (x : M) :
    p.quotEquivOfEqBot hp (Quotient.mk x) = x :=
  rfl

@[simp]
/-
**Submodule.quotEquivOfEqBot_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：quotEquivOfEqBot_symm_apply (hp : p = ⊥) (x : M) : (p.quotEquivOfEqBot hp)
.symm x = (Quotient.mk x)
参数：hp : p = ⊥；x : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem quotEquivOfEqBot_symm_apply (hp : p = ⊥) (x : M) :
    (p.quotEquivOfEqBot hp).symm x = (Quotient.mk x) :=
  rfl

@[simp]
/-
**Submodule.coe_quotEquivOfEqBot_symm** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：coe_quotEquivOfEqBot_symm (hp : p = ⊥) : ((p.quotEquivOfEqBot hp).symm : M
 ->ₗ[R] M ⧸ p) = p.mkQ
参数：hp : p = ⊥。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_quotEquivOfEqBot_symm (hp : p = ⊥) :
    ((p.quotEquivOfEqBot hp).symm : M →ₗ[R] M ⧸ p) = p.mkQ :=
  rfl

@[simp]
/-
**Submodule.Quotient.equiv_refl** 是 Mathlib 中的一个定理，位于命名空间 `Submodule.Quotient`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} [inst : Ring R] [inst_1 : AddCommGroup M] 
[inst_2 : _root_.Module R M]   (P Q : Submodule R M) (hf : Submodule.map (↑(Line
arEquiv.refl R M)) P = Q),   Submodule.Quotient.equiv P Q (LinearEquiv.refl R M)
 hf = P.quotEquivOfEq Q ⋯
参数：P Q : Submodule R M；hf : Submodule.map (↑(LinearEquiv.refl R M)) P = Q；Linear
Equiv.refl R M。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Quotient.equiv_refl (P : Submodule R M) (Q : Submodule R M)
    (hf : P.map (LinearEquiv.refl R M : M →ₗ[R] M) = Q) :
    Quotient.equiv P Q (LinearEquiv.refl R M) hf = quotEquivOfEq _ _ (by simpa using hf) :=
  rfl

end Submodule

end Ring

section CommRing

variable {R M M₂ : Type*} {r : R} {x y : M} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup M₂] [Module R M₂] (p : Submodule R M) (q : Submodule R M₂)

namespace Submodule

/-- Given modules `M`, `M₂` over a commutative ring, together with submodules `p ⊆ M`, `q ⊆ M₂`,
the natural map $\{f ∈ Hom(M, M₂) | f(p) ⊆ q \} \to Hom(M/p, M₂/q)$ is linear. -/
/-
**Submodule.mapQLinear** 是 Mathlib 中的一个定义，位于命名空间 `Submodule`。
形式化陈述：mapQLinear : compatibleMaps p q ->ₗ[R] M ⧸ p ->ₗ[R] M₂ ⧸ q where toFun f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given modules `M`, `M₂` over a commutative ring, together with submodules `p ⊆ M
`, `q ⊆ M₂`,
the natural map $\{f ∈ Hom(M, M₂) | f(p) ⊆ q \} \to Hom(M/p, M₂/q)$ is linear.
-/
def mapQLinear : compatibleMaps p q →ₗ[R] M ⧸ p →ₗ[R] M₂ ⧸ q where
  toFun f := mapQ _ _ f.val f.property
  map_add' x y := by
    ext
    rfl
  map_smul' c f := by
    ext
    rfl

end Submodule

end CommRing

