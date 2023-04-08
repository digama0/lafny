import Lafny.Do

noncomputable example := fun a : Nat => (do'
  if true then
    let xy ← do
      let y ← pure 1
      pure y
    pure xy
  pure 0
: IO Nat)
