Require Import List. 

Require Export Node. 
Require Export Msg.

Require Export EqdepDec

Section EventOrdering.

Inductive NonEmptyTriggerInfo := 
    | msg
    | timeout. 

Definition trigger_info := option NonEmptyTriggerInfo.

Class EventOrdering := 
{

    Event :: Type; 
    
    happensBefore : Event -> Event -> Prop;
    
    loc : Event -> name; 
    
    direct_pred : Event -> option Event;

    trigger : Event -> trigger_info; 
    time : Event -> nat;

    eventDeq: Deq Event;

    
}.

End EventOrdering. 