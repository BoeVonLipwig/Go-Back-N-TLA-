------------------------------- MODULE Sender -------------------------------
EXTENDS Naturals, Integers, TLC, Sequences, Bags, FiniteSets
CONSTANT CORRUPT_DATA, WINDOW_SIZE, MESSAGES, MESSAGE_TYPES
(* --algorithm sender
variables sendData = <<>>, reciveReq = <<>>, toSend = MESSAGES, state = "closed", 
sequenceNum = 1, windowStart = 1, windowEnd = WINDOW_SIZE+1;

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
            if reciveReq[1] = "closing" then 
                skip;
            end if;
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

fair process Connect = "connect"
begin 
A:
    while TRUE do
        await state # "open" /\ state # "closing";
        if state = "closed" \/ (state = "SYN-SENT" /\ reciveReq = <<>>) then
            if  Len(reciveReq) # 4 then
                sendData := <<1, 0, sequenceNum>>;
                state := "SYN-SENT";
            end if;
        elsif (state = "ESTABLISHED" /\ Len(reciveReq) # 1 ) \/ (state = "SYN-SENT" /\ reciveReq # <<>>) then
            if reciveReq[1] = 1 /\ reciveReq[2] = 1 /\  reciveReq[3] = sequenceNum +1 /\ Len(reciveReq) = 4 then 
                sendData := <<0, 1, reciveReq[3], reciveReq[4] + 1>>;
                reciveReq := <<>>;
            end if;
        elsif state = "ESTABLISHED" /\ Len(reciveReq) = 1 then
            state := "open";
        end if;
    end while;
end process;

end algorithm;
*)
\* BEGIN TRANSLATION
\* Label A of process Send at line 16 col 5 changed to A_
VARIABLES sendData, reciveReq, toSend, state, sequenceNum, windowStart, 
          windowEnd

(* define statement *)
MIN(x,y)  == IF (x < y) THEN x ELSE y


vars == << sendData, reciveReq, toSend, state, sequenceNum, windowStart, 
           windowEnd >>

ProcSet == {"send"} \cup {"connect"}

Init == (* Global variables *)
        /\ sendData = <<>>
        /\ reciveReq = <<>>
        /\ toSend = MESSAGES
        /\ state = "closed"
        /\ sequenceNum = 1
        /\ windowStart = 1
        /\ windowEnd = WINDOW_SIZE+1

Send == /\ state = "open"
        /\ sendData = <<>> \/ reciveReq # <<>>
        /\ IF reciveReq # <<>> /\ reciveReq[1] # CORRUPT_DATA
              THEN /\ IF reciveReq[1] = "closing"
                         THEN /\ TRUE
                         ELSE /\ TRUE
                   /\ IF reciveReq[1] > windowStart
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
        /\ UNCHANGED << toSend, state >>

Connect == /\ state # "open" /\ state # "closing"
           /\ IF state = "closed" \/ (state = "SYN-SENT" /\ reciveReq = <<>>)
                 THEN /\ IF Len(reciveReq) # 4
                            THEN /\ sendData' = <<1, 0, sequenceNum>>
                                 /\ state' = "SYN-SENT"
                            ELSE /\ TRUE
                                 /\ UNCHANGED << sendData, state >>
                      /\ UNCHANGED reciveReq
                 ELSE /\ IF (state = "ESTABLISHED" /\Len(reciveReq) = 1 ) \/ (state = "SYN-SENT" /\ reciveReq # <<>>)
                            THEN /\ IF reciveReq[1] = 1 /\ reciveReq[2] = 1 /\  reciveReq[3] = sequenceNum +1 /\ Len(reciveReq) = 4
                                       THEN /\ sendData' = <<0, 1, reciveReq[3], reciveReq[4] + 1>>
                                            /\ reciveReq' = <<>>
                                       ELSE /\ TRUE
                                            /\ UNCHANGED << sendData, 
                                                            reciveReq >>
                                 /\ state' = state
                            ELSE /\ IF state = "ESTABLISHED" /\ Len(reciveReq) = 1
                                       THEN /\ state' = "open"
                                       ELSE /\ TRUE
                                            /\ state' = state
                                 /\ UNCHANGED << sendData, reciveReq >>
           /\ UNCHANGED << toSend, sequenceNum, windowStart, windowEnd >>

Next == Send \/ Connect

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Send)
        /\ WF_vars(Connect)

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
            /\ WF_vars(Connect)
=============================================================================
\* Modification History
\* Last modified Wed Jun 12 20:15:00 NZST 2019 by sdmsi
\* Created Mon Jun 10 00:58:39 NZST 2019 by sdmsi
