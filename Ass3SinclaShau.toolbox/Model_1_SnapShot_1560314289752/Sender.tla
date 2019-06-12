------------------------------- MODULE Sender -------------------------------
EXTENDS Naturals, Integers, TLC, Sequences, Bags, FiniteSets
CONSTANT CORRUPT_DATA, WINDOW_SIZE, MESSAGES, MESSAGE_TYPES
(* --algorithm sender
variables sendData = <<>>, reciveReq = <<>>, toSend = MESSAGES, 
sequenceNum = 1, windowStart = 1, windowEnd = WINDOW_SIZE+1;

define
    MIN(x,y)  == IF (x < y) THEN x ELSE y 
end define;

fair process Send = "send"
begin
A:
(*When the wire is empty and there is data to send, send the data*)
    while TRUE do
        await sendData = <<>> \/ reciveReq # <<>>;
        if reciveReq # <<>> /\ reciveReq[1] # CORRUPT_DATA then 
            if reciveReq[1] > windowStart then
                windowEnd := MIN(WINDOW_SIZE + reciveReq[1], Len(MESSAGES));
                windowStart := reciveReq[1];
            end if;
        end if;
        reciveReq := <<>>;

        if sendData = <<>> /\ toSend # <<>> /\ sequenceNum < Len(toSend) + 1 then
            sendData := <<sequenceNum, toSend[sequenceNum]>>;
            if sequenceNum < windowEnd /\ sequenceNum > windowStart - 1 then
                sequenceNum := sequenceNum + 1;
            else
                sequenceNum := windowStart;
            end if;
        end if;
        
    end while;
end process;

end algorithm;
*)
\* BEGIN TRANSLATION
VARIABLES sendData, reciveReq, toSend, sequenceNum, windowStart, windowEnd

(* define statement *)
MIN(x,y)  == IF (x < y) THEN x ELSE y


vars == << sendData, reciveReq, toSend, sequenceNum, windowStart, windowEnd
        >>

ProcSet == {"send"}

Init == (* Global variables *)
        /\ sendData = <<>>
        /\ reciveReq = <<>>
        /\ toSend = MESSAGES
        /\ sequenceNum = 1
        /\ windowStart = 1
        /\ windowEnd = WINDOW_SIZE+1

Send == /\ sendData = <<>> \/ reciveReq # <<>>
        /\ IF reciveReq # <<>> /\ reciveReq[1] # CORRUPT_DATA
              THEN /\ IF reciveReq[1] > windowStart
                         THEN /\ windowEnd' = MIN(WINDOW_SIZE + reciveReq[1], Len(MESSAGES))
                              /\ windowStart' = reciveReq[1]
                         ELSE /\ TRUE
                              /\ UNCHANGED << windowStart, windowEnd >>
              ELSE /\ TRUE
                   /\ UNCHANGED << windowStart, windowEnd >>
        /\ reciveReq' = <<>>
        /\ IF sendData = <<>> /\ toSend # <<>> /\ sequenceNum < Len(toSend) + 1
              THEN /\ sendData' = <<sequenceNum, toSend[sequenceNum]>>
                   /\ IF sequenceNum < windowEnd' /\ sequenceNum > windowStart' - 1
                         THEN /\ sequenceNum' = sequenceNum + 1
                         ELSE /\ sequenceNum' = windowStart'
              ELSE /\ TRUE
                   /\ UNCHANGED << sendData, sequenceNum >>
        /\ UNCHANGED toSend

Next == Send

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Send)

\* END TRANSLATION

\* checks that the message we are trying to send is of the correcdt type
\*TypeOK == /\ \/ toSend = <<>>
\*             \/ \A i \in DOMAIN toSend : toSend[i] \in MESSAGE_TYPES
             
WinStrOK == /\ windowStart < Len(MESSAGES) + 1 

WinEndOK == /\ windowEnd < Len(MESSAGES) + 1 
            /\ windowEnd = windowStart + WINDOW_SIZE
            
SeqNumOK == /\ sequenceNum > 0
            /\ sequenceNum > windowStart - 1 
            /\ sequenceNum < windowEnd 
            /\ sequenceNum < Len(MESSAGES) + 1 

Invariants == \*/\ TypeOK
              /\ WinStrOK
              /\ WinEndOK
              /\ SeqNumOK
              
              


\* Both of the below proccesses are weakly fair
Fairness == /\ WF_vars(Send)
=============================================================================
\* Modification History
\* Last modified Wed Jun 12 14:23:12 NZST 2019 by sdmsi
\* Created Mon Jun 10 00:58:39 NZST 2019 by sdmsi
