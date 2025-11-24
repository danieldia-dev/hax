
namespace Lean

open Order

universe u v

def Loop.loopCombinator {β : Type u} {m : Type u → Type v} [Monad m]
    (f : Unit → β → m (ForInStep β)) (l : β → m β) (b : β) := do
  match ← f () b with
    | ForInStep.done b => pure b
    | ForInStep.yield b => l b

class Loop.MonoLoopCombinator
    {β : Type u} {m : Type u → Type v} [Monad m] [∀ α, CCPO (m α)]
    (f : Unit → β → m (ForInStep β)) where
  mono : monotone (loopCombinator f) := by unfold Lean.Loop.loopCombinator <;> monotonicity

/-- Our own copy of `Loop.forIn` because the original one is `partial` and thus we cannot reason
about it. -/
@[inline]
def Loop.MonoLoopCombinator.forIn {β : Type u} {m : Type u → Type v} [Monad m] [∀ α, CCPO (m α)]
    (_ : Loop) (init : β) (f : Unit → β → m (ForInStep β)) [MonoLoopCombinator f] :
    m β :=
  let rec @[specialize] loop [MonoLoopCombinator f] (b : β) : m β :=
    loopCombinator f loop b
  partial_fixpoint monotonicity MonoLoopCombinator.mono
  loop init

instance (priority:= high) {m : Type u → Type v} [Monad m] [∀ α, CCPO (m α)]
    [∀ {β : Type u} (f : Unit → β → m (ForInStep β)), Loop.MonoLoopCombinator f] : ForIn m Loop Unit where
  forIn := Loop.forIn

end Lean
