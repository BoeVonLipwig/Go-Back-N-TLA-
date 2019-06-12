------------------------------- MODULE Sender -------------------------------
EXTENDS Naturals, Integers, TLC, Sequences, Bags, FiniteSets
CONSTANT CORRUPT_DATA, WINDOW_SIZE, MESSAGES, MESSAGE_TYPES
(* --algorithm sender
variables sendData = <<>>, reciveReq = <<>>, state = "opening", 
sequenceNum = 1, windowStart = 1, windowEnd = WINDOW_SIZE+1, reqNum = -1;

define
    MIN(x,y)  == IF (x < y) THEN x ELSE y 
end define; 

fair process Send = "send"
begin
A:
(*When the wire is empty and there is data to send, send the data*)
    while TRUE do
        await state = "open" /\ (sendData = <<>> \/ reciveReq # <<>>);
        if reciveReq # <<>> /\ reciveReq[1] # CORRUPT_DATA then 
            if reciveReq[1] = -1 (*Len(MESSAGES)*) then 
                state := "closing";
            end if;
            if reciveReq[1] > windowStart then
                windowEnd := MIN(WINDOW_SIZE + reciveReq[1], Len(MESSAGES));
                windowStart := reciveReq[1];
            end if;
        end if;
        reciveReq := <<>>;

        if sendData = <<>> /\ MESSAGES # <<>> /\ sequenceNum < Len(MESSAGES) + 1 then
            sendData := <<sequenceNum, MESSAGES[sequenceNum]>>;
            if sequenceNum < windowEnd /\ sequenceNum > windowStart - 1 then
                sequenceNum := sequenceNum + 1;
            else
                sequenceNum := windowStart;
            end if;
        end if;
        
    end while;
end process;

fair process SYN = "syn"
begin
A:
    while TRUE do
        await state = "opening" /\ sendData = <<>>;
        if reciveReq # <<>> then 
            if reciveReq # CORRUPT_DATA then 
                if reciveReq[1] = 1 /\ reciveReq[2] = 1 /\ reciveReq[3] = sequenceNum + 1 then 
                    reqNum := reciveReq[4] + 1;
                    state := "SYN_ACK_RECIVED";
                end if;
            end if;
            reciveReq := <<>>;
        end if;
        
        \* spam SYN constantly until successful 
        if state = "opening" then
            sendData := <<1, 0, sequenceNum>>;
        end if;
        
    end while;

end process;

fair process ACK = "ack"
begin 
A: 
    while TRUE do 
        await state = "SYN_ACK_RECIVED";
        \*wait for real data
        if reciveReq # <<>> then 
            if reciveReq # CORRUPT_DATA then 
                if Len(reciveReq) = 1 /\ reciveReq[1] = reqNum -1 then 
                    state := "open"
                else 
                    reciveReq := <<>>;
                end if;
            else 
                reciveReq := <<>>;
            end if;
       end if;
       \* spam ACK
       if state = "SYN_ACK_RECIVED" then 
           sendData := <<0, 1, sequenceNum + 1, reqNum>>;
       end if;
    end while;
end process;


end algorithm;
*)
\* BEGIN TRANSLATION
\* Label A of process Send at line 16 col 5 changed to A_
\* Label A of process SYN at line 44 col 5 changed to A_S
VARIABLES sendData, reciveReq, state, sequenceNum, windowStart, windowEnd, 
          reqNum

(* define statement *)
MIN(x,y)  == IF (x < y) THEN x ELSE y


vars == << sendData, reciveReq, state, sequenceNum, windowStart, windowEnd, 
           reqNum >>

ProcSet == {"send"} \cup {"syn"} \cup {"ack"}

Init == (* Global variables *)
        /\ sendData = <<>>
        /\ reciveReq = <<>>
        /\ state = "opening"
        /\ sequenceNum = 1
        /\ windowStart = 1
        /\ windowEnd = WINDOW_SIZE+1
        /\ reqNum = -1

Send == /\ state = "open" /\ (sendData = <<>> \/ reciveReq # <<>>)
        /\ IF reciveReq # <<>> /\ reciveReq[1] # CORRUPT_DATA
              THEN /\ IF reciveReq[1] = -1
                         THEN /\ state' = "closing"
                         ELSE /\ TRUE
                              /\ state' = state
                   /\ IF reciveReq[1] > windowStart
                         THEN /\ windowEnd' = MIN(WINDOW_SIZE + reciveReq[1], Len(MESSAGES))
                              /\ windowStart' = reciveReq[1]
                         ELSE /\ TRUE
                              /\ UNCHANGED << windowStart, windowEnd >>
              ELSE /\ TRUE
                   /\ UNCHANGED << state, windowStart, windowEnd >>
        /\ reciveReq' = <<>>
        /\ IF sendData = <<>> /\ MESSAGES # <<>> /\ sequenceNum < Len(MESSAGES) + 1
              THEN /\ sendData' = <<sequenceNum, MESSAGES[sequenceNum]>>
                   /\ IF sequenceNum < windowEnd' /\ sequenceNum > windowStart' - 1
                         THEN /\ sequenceNum' = sequenceNum + 1
                         ELSE /\ sequenceNum' = windowStart'
              ELSE /\ TRUE
                   /\ UNCHANGED << sendData, sequenceNum >>
        /\ UNCHANGED reqNum

SYN == /\ state = "opening" /\ sendData = <<>>
       /\ IF reciveReq # <<>>
             THEN /\ IF reciveReq # CORRUPT_DATA
                        THEN /\ IF reciveReq[1] = 1 /\ reciveReq[2] = 1 /\ reciveReq[3] = sequenceNum + 1
                                   THEN /\ reqNum' = reciveReq[4] + 1
                                        /\ state' = "SYN_ACK_RECIVED"
                                   ELSE /\ TRUE
                                        /\ UNCHANGED << state, reqNum >>
                        ELSE /\ TRUE
                             /\ UNCHANGED << state, reqNum >>
                  /\ reciveReq' = <<>>
             ELSE /\ TRUE
                  /\ UNCHANGED << reciveReq, state, reqNum >>
       /\ IF state' = "opening"
             THEN /\ sendData' = <<1, 0, sequenceNum>>
             ELSE /\ TRUE
                  /\ UNCHANGED sendData
       /\ UNCHANGED << sequenceNum, windowStart, windowEnd >>

ACK == /\ state = "SYN_ACK_RECIVED"
       /\ IF reciveReq # <<>>
             THEN /\ IF reciveReq # CORRUPT_DATA
                        THEN /\ IF Len(reciveReq) = 1 /\ reciveReq[1] = reqNum -1
                                   THEN /\ state' = "open"
                                        /\ UNCHANGED reciveReq
                                   ELSE /\ reciveReq' = <<>>
                                        /\ state' = state
                        ELSE /\ reciveReq' = <<>>
                             /\ state' = state
             ELSE /\ TRUE
                  /\ UNCHANGED << reciveReq, state >>
       /\ IF state' = "SYN_ACK_RECIVED"
             THEN /\ sendData' = <<0, 1, sequenceNum + 1, reqNum>>
             ELSE /\ TRUE
                  /\ UNCHANGED sendData
       /\ UNCHANGED << sequenceNum, windowStart, windowEnd, reqNum >>

Next == Send \/ SYN \/ ACK

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Send)
        /\ WF_vars(SYN)
        /\ WF_vars(ACK)

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

Properties == \A x \in {"opening", "SYN_ACK_RECIVED", "open"}: <>( state = x )
              


\* Both of the below proccesses are weakly fair
Fairness == /\ WF_vars(Send)
            /\ WF_vars(SYN)
            /\ WF_vars(ACK)
=============================================================================
\* Modification History
\* Last modified Wed Jun 12 23:18:52 NZST 2019 by sdmsi
\* Created Mon Jun 10 00:58:39 NZST 2019 by sdmsi
