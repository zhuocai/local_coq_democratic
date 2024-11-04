Require Export Node. 

Section Node. 

Class Msg := MkMsg {msg : Type}.

Context {m : Msg}.

Record DirectedMsg := 
MkDMsg
{
    dmMsg : msg; 
    dmDst : list name; 
    dmDelay : nat; 
}.

Definition DirectedMsgs := list DirectedMsg. 

End Node. 