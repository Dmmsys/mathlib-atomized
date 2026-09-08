/-
Copyright (c) 2021 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot
-/
module

public import Mathlib.Analysis.Normed.Group.Hom
public import Mathlib.Analysis.Normed.Group.Completion

/-!
# Completion of normed group homs

Given two (semi) normed groups `G` and `H` and a normed group hom `f : NormedAddGroupHom G H`,
we build and study a normed group hom
`f.completion : NormedAddGroupHom (completion G) (completion H)` such that the diagram

```
                   f
     G       ----------->     H

     |                        |
     |                        |
     |                        |
     V                        V

completion G -----------> completion H
            f.completion
```

commutes. The map itself comes from the general theory of completion of uniform spaces, but here
we want a normed group hom, study its operator norm and kernel.

The vertical maps in the above diagrams are also normed group homs constructed in this file.

## Main definitions and results:

* `NormedAddGroupHom.completion`: see the discussion above.
* `NormedAddCommGroup.toCompl : NormedAddGroupHom G (completion G)`: the canonical map from
  `G` to its completion, as a normed group hom
* `NormedAddGroupHom.completion_toCompl`: the above diagram indeed commutes.
* `NormedAddGroupHom.norm_completion`: `‖f.completion‖ = ‖f‖`
* `NormedAddGroupHom.ker_le_ker_completion`: the kernel of `f.completion` contains the image of
  the kernel of `f`.
* `NormedAddGroupHom.ker_completion`: the kernel of `f.completion` is the closure of the image of
  the kernel of `f` under an assumption that `f` is quantitatively surjective onto its image.
* `NormedAddGroupHom.extension` : if `H` is complete, the extension of
  `f : NormedAddGroupHom G H` to a `NormedAddGroupHom (completion G) H`.
-/

@[expose] public section


noncomputable section

open Set NormedAddGroupHom UniformSpace

section Completion

variable {G : Type*} [SeminormedAddCommGroup G] {H : Type*} [SeminormedAddCommGroup H]
  {K : Type*} [SeminormedAddCommGroup K]

/-- The normed group hom induced between completions. -/
/-
**NormedAddGroupHom.completion** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：NormedAddGroupHom.completion (f : NormedAddGroupHom G H) : NormedAddGroupH
om (Completion G) (Completion H)
参数：f : NormedAddGroupHom G H。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `NormedAddGroupHom.continuous`：∀ {V₁ : Type u_2} {V₂ : Type u_3} [inst : 
SeminormedAddCommGroup V₁] [inst_1 : SeminormedAddCommGroup V₂]   (f : NormedAdd
GroupHom V₁ V₂), C…
· 使用定理 `NormedAddGroupHom.opNorm_nonneg`：opNorm_nonneg : 0 <= ‖f‖

--- 原说明 ---
The normed group hom induced between completions.
-/
def NormedAddGroupHom.completion (f : NormedAddGroupHom G H) :
    NormedAddGroupHom (Completion G) (Completion H) :=
  .ofLipschitz (f.toAddMonoidHom.completion f.continuous) f.lipschitz.completion_map
/-
**NormedAddGroupHom.completion_def** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：NormedAddGroupHom.completion_def (f : NormedAddGroupHom G H) (x : Completi
on G) : f.completion x = Completion.map f x
参数：f : NormedAddGroupHom G H；x : Completion G。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem NormedAddGroupHom.completion_def (f : NormedAddGroupHom G H) (x : Completion G) :
    f.completion x = Completion.map f x :=
  rfl

@[simp]
/-
**NormedAddGroupHom.completion_coe_to_fun** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：NormedAddGroupHom.completion_coe_to_fun (f : NormedAddGroupHom G H) : (f.c
ompletion : Completion G -> Completion H) = Completion.map f
参数：f : NormedAddGroupHom G H。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem NormedAddGroupHom.completion_coe_to_fun (f : NormedAddGroupHom G H) :
    (f.completion : Completion G → Completion H) = Completion.map f := rfl
/-
**NormedAddGroupHom.completion_coe** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：NormedAddGroupHom.completion_coe (f : NormedAddGroupHom G H) (g : G) : f.c
ompletion g = f g
参数：f : NormedAddGroupHom G H；g : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformSpace.Completion.map_coe`：map_coe (hf : UniformContinuous f) (a :
 α) : (Completion.map f) a = f a
· 使用定理 `NormedAddGroupHom.uniformContinuous`：∀ {V₁ : Type u_2} {V₂ : Type u_3} [
inst : SeminormedAddCommGroup V₁] [inst_1 : SeminormedAddCommGroup V₂]   (f : No
rmedAddGroupHom V₁ V₂), U…
-/
theorem NormedAddGroupHom.completion_coe (f : NormedAddGroupHom G H) (g : G) :
    f.completion g = f g :=
  Completion.map_coe f.uniformContinuous _

@[simp]
/-
**NormedAddGroupHom.completion_coe'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：NormedAddGroupHom.completion_coe' (f : NormedAddGroupHom G H) (g : G) : Co
mpletion.map f g = f g
参数：f : NormedAddGroupHom G H；g : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NormedAddGroupHom.completion_coe`：NormedAddGroupHom.completion_coe (f : 
NormedAddGroupHom G H) (g : G) : f.completion g = f g
-/
theorem NormedAddGroupHom.completion_coe' (f : NormedAddGroupHom G H) (g : G) :
    Completion.map f g = f g :=
  f.completion_coe g

/-- Completion of normed group homs as a normed group hom. -/
@[simps]
/-
**normedAddGroupHomCompletionHom** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：normedAddGroupHomCompletionHom : NormedAddGroupHom G H ->+ NormedAddGroupH
om (Completion G) (Completion H) where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Completion of normed group homs as a normed group hom.
-/
def normedAddGroupHomCompletionHom :
    NormedAddGroupHom G H →+ NormedAddGroupHom (Completion G) (Completion H) where
  toFun := NormedAddGroupHom.completion
  map_zero' := toAddMonoidHom_injective AddMonoidHom.completion_zero
  map_add' f g := toAddMonoidHom_injective <|
    f.toAddMonoidHom.completion_add g.toAddMonoidHom f.continuous g.continuous

@[simp]
/-
**NormedAddGroupHom.completion_id** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：NormedAddGroupHom.completion_id : (NormedAddGroupHom.id G).completion = No
rmedAddGroupHom.id (Completion G)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NormedAddGroupHom.ext`：ext (H : forall x, f x = g x) : f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NormedAddGroupHom.completion_def`：NormedAddGroupHom.completion_def (f : 
NormedAddGroupHom G H) (x : Completion G) : f.completion x = Completion.map f x
· 使用定理 `NormedAddGroupHom.coe_id`：coe_id : (NormedAddGroupHom.id V : V -> V) = _
root_.id
· 使用定理 `UniformSpace.Completion.map_id`：map_id : Completion.map (@id α) = id
-/
theorem NormedAddGroupHom.completion_id :
    (NormedAddGroupHom.id G).completion = NormedAddGroupHom.id (Completion G) := by
  ext x
  rw [NormedAddGroupHom.completion_def, NormedAddGroupHom.coe_id, Completion.map_id]
  rfl
/-
**NormedAddGroupHom.completion_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：NormedAddGroupHom.completion_comp (f : NormedAddGroupHom G H) (g : NormedA
ddGroupHom H K) : g.completion.comp f.completion = (g.comp f).completion
参数：f : NormedAddGroupHom G H；g : NormedAddGroupHom H K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NormedAddGroupHom.ext`：ext (H : forall x, f x = g x) : f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NormedAddGroupHom.coe_comp`：coe_comp (f : NormedAddGroupHom V₁ V₂) (g : 
NormedAddGroupHom V₂ V₃) : (g.comp f : V₁ -> V₃) = (g : V₂ -> V₃) ∘ (f : V₁ -> V
₂)
· 使用定理 `NormedAddGroupHom.completion_def`：NormedAddGroupHom.completion_def (f : 
NormedAddGroupHom G H) (x : Completion G) : f.completion x = Completion.map f x
· 使用定理 `NormedAddGroupHom.completion_coe_to_fun`：NormedAddGroupHom.completion_co
e_to_fun (f : NormedAddGroupHom G H) : (f.completion : Completion G -> Completio
n H) = Completion.map f
· 使用定理 `UniformSpace.Completion.map_comp`：map_comp {g : β -> γ} {f : α -> β} (hg
 : UniformContinuous g) (hf : UniformContinuous f) : Completion.map g ∘ Completi
on.map f = Completion.…
· 使用定理 `NormedAddGroupHom.uniformContinuous`：∀ {V₁ : Type u_2} {V₂ : Type u_3} [
inst : SeminormedAddCommGroup V₁] [inst_1 : SeminormedAddCommGroup V₂]   (f : No
rmedAddGroupHom V₁ V₂), U…
-/
theorem NormedAddGroupHom.completion_comp (f : NormedAddGroupHom G H) (g : NormedAddGroupHom H K) :
    g.completion.comp f.completion = (g.comp f).completion := by
  ext x
  rw [NormedAddGroupHom.coe_comp, NormedAddGroupHom.completion_def,
    NormedAddGroupHom.completion_coe_to_fun, NormedAddGroupHom.completion_coe_to_fun,
    Completion.map_comp g.uniformContinuous f.uniformContinuous]
  rfl
/-
**NormedAddGroupHom.completion_neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：NormedAddGroupHom.completion_neg (f : NormedAddGroupHom G H) : (-f).comple
tion = -f.completion
参数：f : NormedAddGroupHom G H。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
-/
theorem NormedAddGroupHom.completion_neg (f : NormedAddGroupHom G H) :
    (-f).completion = -f.completion :=
  map_neg (normedAddGroupHomCompletionHom : NormedAddGroupHom G H →+ _) f
/-
**NormedAddGroupHom.completion_add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：NormedAddGroupHom.completion_add (f g : NormedAddGroupHom G H) : (f + g).c
ompletion = f.completion + g.completion
参数：f g : NormedAddGroupHom G H。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidHom.map_add`：∀ {M : Type u_4} {N : Type u_5} [inst : AddZero M]
 [inst_1 : AddZero N] (f : M →+ N) (a b : M), f (a + b) = f a + f b
-/
theorem NormedAddGroupHom.completion_add (f g : NormedAddGroupHom G H) :
    (f + g).completion = f.completion + g.completion :=
  normedAddGroupHomCompletionHom.map_add f g
/-
**NormedAddGroupHom.completion_sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：NormedAddGroupHom.completion_sub (f g : NormedAddGroupHom G H) : (f - g).c
ompletion = f.completion - g.completion
参数：f g : NormedAddGroupHom G H。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
-/
theorem NormedAddGroupHom.completion_sub (f g : NormedAddGroupHom G H) :
    (f - g).completion = f.completion - g.completion :=
  map_sub (normedAddGroupHomCompletionHom : NormedAddGroupHom G H →+ _) f g

@[simp]
/-
**NormedAddGroupHom.zero_completion** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：NormedAddGroupHom.zero_completion : (0 : NormedAddGroupHom G H).completion
 = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidHom.map_zero`：∀ {M : Type u_4} {N : Type u_5} [inst : AddZero M
] [inst_1 : AddZero N] (f : M →+ N), f 0 = 0
-/
theorem NormedAddGroupHom.zero_completion : (0 : NormedAddGroupHom G H).completion = 0 :=
  normedAddGroupHomCompletionHom.map_zero

/-- The map from a normed group to its completion, as a normed group hom. -/
@[simps]
/-
**NormedAddCommGroup.toCompl** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：NormedAddCommGroup.toCompl : NormedAddGroupHom G (Completion G) where toFu
n
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map from a normed group to its completion, as a normed group hom.
-/
def NormedAddCommGroup.toCompl : NormedAddGroupHom G (Completion G) where
  toFun := (↑)
  map_add' := Completion.toCompl.map_add
  bound' := ⟨1, by simp⟩

open NormedAddCommGroup
/-
**NormedAddCommGroup.norm_toCompl** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：NormedAddCommGroup.norm_toCompl (x : G) : ‖toCompl x‖ = ‖x‖
参数：x : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformSpace.Completion.norm_coe`：norm_coe {E} [SeminormedAddCommGroup E
] (x : E) : ‖(x : Completion E)‖ = ‖x‖
-/
theorem NormedAddCommGroup.norm_toCompl (x : G) : ‖toCompl x‖ = ‖x‖ :=
  Completion.norm_coe x
/-
**NormedAddCommGroup.denseRange_toCompl** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：NormedAddCommGroup.denseRange_toCompl : DenseRange (toCompl : G -> Complet
ion G)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDenseInducing.dense`：∀ {α : Type u_1} {β : Type u_2} [inst : Topologic
alSpace α] [inst_1 : TopologicalSpace β] {i : α → β},   IsDenseInducing i → Dens
eRange i
· 使用定理 `UniformSpace.Completion.isDenseInducing_coe`：isDenseInducing_coe : IsDen
seInducing ((↑) : α -> Completion α)
-/
theorem NormedAddCommGroup.denseRange_toCompl : DenseRange (toCompl : G → Completion G) :=
  Completion.isDenseInducing_coe.dense

@[simp]
/-
**NormedAddGroupHom.completion_toCompl** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：NormedAddGroupHom.completion_toCompl (f : NormedAddGroupHom G H) : f.compl
etion.comp toCompl = toCompl.comp f
参数：f : NormedAddGroupHom G H。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NormedAddGroupHom.ext`：ext (H : forall x, f x = g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NormedAddGroupHom.comp_apply`：∀ {V₁ : Type u_2} {V₂ : Type u_3} {V₃ : Ty
pe u_4} [inst : SeminormedAddCommGroup V₁]   [inst_1 : SeminormedAddCommGroup V₂
] [inst_2 : Semino…
· 使用定理 `NormedAddCommGroup.toCompl_apply`：∀ {G : Type u_1} [inst : SeminormedAdd
CommGroup G] (a : G), NormedAddCommGroup.toCompl a = ↑a
· 使用定理 `NormedAddGroupHom.completion_coe'`：NormedAddGroupHom.completion_coe' (f 
: NormedAddGroupHom G H) (g : G) : Completion.map f g = f g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem NormedAddGroupHom.completion_toCompl (f : NormedAddGroupHom G H) :
    f.completion.comp toCompl = toCompl.comp f := by ext x; simp

@[simp]
/-
**NormedAddGroupHom.norm_completion** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：NormedAddGroupHom.norm_completion (f : NormedAddGroupHom G H) : ‖f.complet
ion‖ = ‖f‖
参数：f : NormedAddGroupHom G H。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `NormedAddGroupHom.ofLipschitz_norm_le`：ofLipschitz_norm_le (f : V₁ ->+ V
₂) {K : Real>=0} (h : LipschitzWith K f) : ‖ofLipschitz f h‖ <= K
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `NormedAddGroupHom.continuous`：∀ {V₁ : Type u_2} {V₂ : Type u_3} [inst : 
SeminormedAddCommGroup V₁] [inst_1 : SeminormedAddCommGroup V₂]   (f : NormedAdd
GroupHom V₁ V₂), C…
· 使用定理 `NormedAddGroupHom.opNorm_nonneg`：opNorm_nonneg : 0 <= ‖f‖
· 使用定理 `NormedAddGroupHom.opNorm_le_bound`：opNorm_le_bound {M : Real} (hMp : 0 <
= M) (hM : forall x, ‖f x‖ <= M * ‖x‖) : ‖f‖ <= M
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `NormedAddGroupHom.completion_coe'`：NormedAddGroupHom.completion_coe' (f 
: NormedAddGroupHom G H) (g : G) : Completion.map f g = f g
· 使用定理 `UniformSpace.Completion.norm_coe`：norm_coe {E} [SeminormedAddCommGroup E
] (x : E) : ‖(x : Completion E)‖ = ‖x‖
· 使用定理 `NormedAddGroupHom.le_opNorm`：le_opNorm (x : V₁) : ‖f x‖ <= ‖f‖ * ‖x‖
-/
theorem NormedAddGroupHom.norm_completion (f : NormedAddGroupHom G H) : ‖f.completion‖ = ‖f‖ :=
  le_antisymm (ofLipschitz_norm_le _ _) <| opNorm_le_bound _ (norm_nonneg _) fun x => by
    simpa using f.completion.le_opNorm x
/-
**NormedAddGroupHom.ker_le_ker_completion** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：NormedAddGroupHom.ker_le_ker_completion (f : NormedAddGroupHom G H) : (toC
ompl.comp <| incl f.ker).range <= f.completion.ker
参数：f : NormedAddGroupHom G H。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NormedAddGroupHom.comp_apply`：∀ {V₁ : Type u_2} {V₂ : Type u_3} {V₃ : Ty
pe u_4} [inst : SeminormedAddCommGroup V₁]   [inst_1 : SeminormedAddCommGroup V₂
] [inst_2 : Semino…
· 使用定理 `NormedAddGroupHom.incl_apply`：∀ {V : Type u_1} [inst : SeminormedAddComm
Group V] (s : AddSubgroup V) (self : ↥s),   (NormedAddGroupHom.incl s) self = ↑s
elf
· 使用定理 `NormedAddCommGroup.toCompl_apply`：∀ {G : Type u_1} [inst : SeminormedAdd
CommGroup G] (a : G), NormedAddCommGroup.toCompl a = ↑a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `NormedAddGroupHom.completion_coe'`：NormedAddGroupHom.completion_coe' (f 
: NormedAddGroupHom G H) (g : G) : Completion.map f g = f g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem NormedAddGroupHom.ker_le_ker_completion (f : NormedAddGroupHom G H) :
    (toCompl.comp <| incl f.ker).range ≤ f.completion.ker := by
  rintro _ ⟨⟨g, h₀ : f g = 0⟩, rfl⟩
  simp [h₀, mem_ker, Completion.coe_zero]
/-
**NormedAddGroupHom.ker_completion** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：NormedAddGroupHom.ker_completion {f : NormedAddGroupHom G H} {C : Real} (h
 : f.SurjectiveOnWith f.range C) : (f.completion.ker : Set <| Completion G) = cl
osure (toCompl.comp <| incl f.ker).range
参数：h : f.SurjectiveOnWith f.range C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SeminormedAddCommGroup.mem_closure_iff`：∀ {E : Type u_4} [inst : Seminor
medAddCommGroup E] {a : E} {s : Set E},   a ∈ closure s ↔ ∀ (ε : ℝ), 0 < ε → ∃ b
 ∈ s, ‖a - b‖ < ε
· 使用定理 `NormedAddGroupHom.SurjectiveOnWith.exists_pos`：∀ {V₁ : Type u_2} {V₂ : T
ype u_3} [inst : SeminormedAddCommGroup V₁] [inst_1 : SeminormedAddCommGroup V₂]
   {f : NormedAddGroupHom V₁ V₂} {K…
· 使用定理 `exists_pos_mul_lt`：exists_pos_mul_lt {a : α} (h : 0 < a) (b : α) : exist
s c : α, 0 < c ∧ b * c < a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsDenseInducing.dense`：∀ {α : Type u_1} {β : Type u_2} [inst : Topologic
alSpace α] [inst_1 : TopologicalSpace β] {i : α → β},   IsDenseInducing i → Dens
eRange i
· 使用定理 `UniformSpace.Completion.isDenseInducing_coe`：isDenseInducing_coe : IsDen
seInducing ((↑) : α -> Completion α)
· 使用定理 `NormedAddGroupHom.mem_range_self`：mem_range_self (v : V₁) : f v in f.ran
ge
· 使用定理 `NormedAddGroupHom.mem_ker`：mem_ker (v : V₁) : v in f.ker ↔ f v = 0
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `NormedAddGroupHom.completion_coe'`：NormedAddGroupHom.completion_coe' (f 
: NormedAddGroupHom G H) (g : G) : Completion.map f g = f g
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用定理 `norm_neg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), ‖-a‖ =
 ‖a‖
· 使用定理 `UniformSpace.Completion.norm_coe`：norm_coe {E} [SeminormedAddCommGroup E
] (x : E) : ‖(x : Completion E)‖ = ‖x‖
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `NormedAddGroupHom.norm_completion`：NormedAddGroupHom.norm_completion (f 
: NormedAddGroupHom G H) : ‖f.completion‖ = ‖f‖
· 使用定理 `NormedAddGroupHom.le_opNorm`：le_opNorm (x : V₁) : ‖f x‖ <= ‖f‖ * ‖x‖
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `UniformSpace.Completion.coe_sub`：coe_sub (a b : α) : ((a - b : α) : Comp
letion α) = a - b
· 使用定理 `sub_add`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b c : α), 
a - b + c = a - (b - c)
（共 48 条，此处仅展示前 30 条）
-/
theorem NormedAddGroupHom.ker_completion {f : NormedAddGroupHom G H} {C : ℝ}
    (h : f.SurjectiveOnWith f.range C) :
    (f.completion.ker : Set <| Completion G) = closure (toCompl.comp <| incl f.ker).range := by
  refine le_antisymm ?_ (closure_minimal f.ker_le_ker_completion f.completion.isClosed_ker)
  rintro hatg (hatg_in : f.completion hatg = 0)
  rw [SeminormedAddCommGroup.mem_closure_iff]
  intro ε ε_pos
  rcases h.exists_pos with ⟨C', C'_pos, hC'⟩
  rcases exists_pos_mul_lt ε_pos (1 + C' * ‖f‖) with ⟨δ, δ_pos, hδ⟩
  obtain ⟨_, ⟨g : G, rfl⟩, hg : ‖hatg - g‖ < δ⟩ :=
    SeminormedAddCommGroup.mem_closure_iff.mp (Completion.isDenseInducing_coe.dense hatg) δ δ_pos
  obtain ⟨g' : G, hgg' : f g' = f g, hfg : ‖g'‖ ≤ C' * ‖f g‖⟩ := hC' (f g) (mem_range_self _ g)
  have mem_ker : g - g' ∈ f.ker := by rw [f.mem_ker, map_sub, sub_eq_zero.mpr hgg'.symm]
  refine ⟨_, ⟨⟨g - g', mem_ker⟩, rfl⟩, ?_⟩
  have : ‖f g‖ ≤ ‖f‖ * δ := calc
    ‖f g‖ ≤ ‖f‖ * ‖hatg - g‖ := by
      simpa [map_sub, hatg_in] using f.completion.le_opNorm (hatg - g)
    _ ≤ ‖f‖ * δ := by gcongr
  calc ‖hatg - ↑(g - g')‖ = ‖hatg - g + g'‖ := by rw [Completion.coe_sub, sub_add]
    _ ≤ ‖hatg - g‖ + ‖(g' : Completion G)‖ := norm_add_le _ _
    _ = ‖hatg - g‖ + ‖g'‖ := by rw [Completion.norm_coe]
    _ < δ + C' * ‖f g‖ := add_lt_add_of_lt_of_le hg hfg
    _ ≤ δ + C' * (‖f‖ * δ) := by gcongr
    _ < ε := by simpa only [add_mul, one_mul, mul_assoc] using hδ

end Completion

section Extension

variable {G : Type*} [SeminormedAddCommGroup G]
variable {H : Type*} [SeminormedAddCommGroup H] [T0Space H] [CompleteSpace H]

/-- If `H` is complete, the extension of `f : NormedAddGroupHom G H` to a
`NormedAddGroupHom (completion G) H`. -/
/-
**NormedAddGroupHom.extension** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：NormedAddGroupHom.extension (f : NormedAddGroupHom G H) : NormedAddGroupHo
m (Completion G) H
参数：f : NormedAddGroupHom G H。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `NormedAddGroupHom.continuous`：∀ {V₁ : Type u_2} {V₂ : Type u_3} [inst : 
SeminormedAddCommGroup V₁] [inst_1 : SeminormedAddCommGroup V₂]   (f : NormedAdd
GroupHom V₁ V₂), C…
· 使用定理 `NormedAddGroupHom.opNorm_nonneg`：opNorm_nonneg : 0 <= ‖f‖

--- 原说明 ---
If `H` is complete, the extension of `f : NormedAddGroupHom G H` to a
`NormedAddGroupHom (completion G) H`.
-/
def NormedAddGroupHom.extension (f : NormedAddGroupHom G H) : NormedAddGroupHom (Completion G) H :=
  .ofLipschitz (f.toAddMonoidHom.extension f.continuous) <|
    let _ := MetricSpace.ofT0PseudoMetricSpace H
    f.lipschitz.completion_extension
/-
**NormedAddGroupHom.extension_def** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：NormedAddGroupHom.extension_def (f : NormedAddGroupHom G H) (v : G) : f.ex
tension v = Completion.extension f v
参数：f : NormedAddGroupHom G H；v : G。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem NormedAddGroupHom.extension_def (f : NormedAddGroupHom G H) (v : G) :
    f.extension v = Completion.extension f v :=
  rfl

@[simp]
/-
**NormedAddGroupHom.extension_coe** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：NormedAddGroupHom.extension_coe (f : NormedAddGroupHom G H) (v : G) : f.ex
tension v = f v
参数：f : NormedAddGroupHom G H；v : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidHom.extension_coe`：AddMonoidHom.extension_coe [CompleteSpace β]
 [T0Space β] (f : α ->+ β) (hf : Continuous f) (a : α) : f.extension hf a = f a
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `NormedAddGroupHom.continuous`：∀ {V₁ : Type u_2} {V₂ : Type u_3} [inst : 
SeminormedAddCommGroup V₁] [inst_1 : SeminormedAddCommGroup V₂]   (f : NormedAdd
GroupHom V₁ V₂), C…
-/
theorem NormedAddGroupHom.extension_coe (f : NormedAddGroupHom G H) (v : G) : f.extension v = f v :=
  AddMonoidHom.extension_coe _ f.continuous _
/-
**NormedAddGroupHom.extension_coe_to_fun** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：NormedAddGroupHom.extension_coe_to_fun (f : NormedAddGroupHom G H) : (f.ex
tension : Completion G -> H) = Completion.extension f
参数：f : NormedAddGroupHom G H。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem NormedAddGroupHom.extension_coe_to_fun (f : NormedAddGroupHom G H) :
    (f.extension : Completion G → H) = Completion.extension f :=
  rfl
/-
**NormedAddGroupHom.extension_unique** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：NormedAddGroupHom.extension_unique (f : NormedAddGroupHom G H) {g : Normed
AddGroupHom (Completion G) H} (hg : forall v, f v = g v) : f.extension = g
参数：f : NormedAddGroupHom G H；Completion G；hg : forall v, f v = g v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NormedAddGroupHom.ext`：ext (H : forall x, f x = g x) : f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NormedAddGroupHom.extension_coe_to_fun`：NormedAddGroupHom.extension_coe_
to_fun (f : NormedAddGroupHom G H) : (f.extension : Completion G -> H) = Complet
ion.extension f
· 使用定理 `UniformSpace.Completion.extension_unique`：extension_unique (hf : Uniform
Continuous f) {g : Completion α -> β} (hg : UniformContinuous g) (h : forall a :
 α, f a = g (a : Completion α)…
· 使用定理 `NormedAddGroupHom.uniformContinuous`：∀ {V₁ : Type u_2} {V₂ : Type u_3} [
inst : SeminormedAddCommGroup V₁] [inst_1 : SeminormedAddCommGroup V₂]   (f : No
rmedAddGroupHom V₁ V₂), U…
-/
theorem NormedAddGroupHom.extension_unique (f : NormedAddGroupHom G H)
    {g : NormedAddGroupHom (Completion G) H} (hg : ∀ v, f v = g v) : f.extension = g := by
  ext v
  rw [NormedAddGroupHom.extension_coe_to_fun,
    Completion.extension_unique f.uniformContinuous g.uniformContinuous fun a => hg a]

end Extension

