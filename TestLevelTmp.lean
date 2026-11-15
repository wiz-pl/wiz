import Wiz.Core.Level

open Wiz

def u : Level := .param "u"
def v : Level := .param "v"

#eval Level.normalize (Level.max (Level.succ u) (Level.succ v))
#eval Level.shiftDown (Level.normalize (Level.max (Level.succ u) (Level.succ v))) 1
#eval Level.ofNF (Level.normalize (Level.max u v))
#eval Level.metavarOffset? (Level.normalize (Level.succ (.mvar 2)))
#eval Level.normalize (Level.ofNF (Level.normalize (Level.max u v)) |>.succ)
