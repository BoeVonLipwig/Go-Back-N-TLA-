------------------------------- MODULE Sender -------------------------------
EXTENDS Naturals, Integers, TLC, Sequences, Bags, FiniteSets
CONSTANT CORRUPT_DATA, WINDOW_SIZE, MESSAGES, MESSAGE_TYPES
(* --algorithm sender
variables sendData = <<>>, receiveReq = <<>>, state = "opening", 
sequenceNum = 1, windowStart = 1, windowEnd = WINDOW_SIZE+1, reqNum = -1;

define
    MIN(x,y)  == IF (x < y) THEN x ELSE y 
end define; 

fair process Send = "send"
begin
A:
(*When the wire is empty and there is data to send, send the data*)
    while TRUE do
        await state = "open" /\ (sendData = <<>> \/ receiveReq # <<>>);
        if receiveReq # <<>> /\ receiveReq[1] # CORRUPT_DATA then 
            if receiveReq[1] = Len(MESSAGES) + 1 then 
                state := "SENDING_FIN";
            \* check for error here later
            elsif receiveReq[1] > windowStart then
                windowEnd := MIN(WINDOW_SIZE + receiveReq[1], Len(MESSAGES));
                windowStart := receiveReq[1];
            end if;
        end if;
        receiveReq := <<>>;

        if sendData = <<>> /\ MESSAGES # <<>> /\ sequenceNum < Len(MESSAGES) + 1 /\ state # "closing" then
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
        if receiveReq # <<>> then 
            if receiveReq # CORRUPT_DATA then 
                if receiveReq[1] = 1 /\ receiveReq[2] = 1 /\ receiveReq[3] = sequenceNum + 1 then 
                    reqNum := receiveReq[4] + 1;
                    state := "SYN_ACK_RECEIVED";
                end if;
            end if;
            receiveReq := <<>>;
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
        await state = "SYN_ACK_RECEIVED";
        \*wait for real data
        if receiveReq # <<>> then 
            if receiveReq # CORRUPT_DATA then 
                if Len(receiveReq) = 1 /\ receiveReq[1] = reqNum -1 then 
                    state := "open"
                else 
                    receiveReq := <<>>;
                end if;
            else 
                receiveReq := <<>>;
            end if;
       end if;
       \* spam ACK
       if state = "SYN_ACK_RECEIVED" then 
           sendData := <<0, 1, sequenceNum + 1, reqNum>>;
       end if;
    end while;
end process;

fair process FIN = "fin"
begin 
A: 
    while TRUE do 
        await state = "SENDING_FIN";
        if receiveReq # <<>> then
            if receiveReq # CORRUPT_DATA then
                if receiveReq[1] = -2 /\ receiveReq[2] = "FIN-ACK" then 
                    state := "RECEIVED_FIN-ACK";
                end if;
            end if;
        end if;
        receiveReq := <<>>;
        if state = "SENDING_FIN" then
            sendData := <<-1, "FIN">>;
        end if;
    end while;
end process;

fair process FINACK = "finack"
begin 
A: 
    while TRUE do 
        await (state = "RECEIVED_FIN-ACK" \/ state = "Closed");
        
        (* since we cant prove this message has been received by the sender and we cant time this out 
           we will just send it forever as tla does not allow us to fully implement tcp*)
        
        state := "Closed";
        sendData := <<-3, "ACK">>;
    end while;
end process;


end algorithm;
*)
\* BEGIN TRANSLATION
\* Label A of process Send at line 16 col 5 changed to A_
\* Label A of process SYN at line 44 col 5 changed to A_S
\* Label A of process ACK at line 68 col 5 changed to A_A
\* Label A of process FIN at line 92 col 5 changed to A_F
VARIABLES sendData, receiveReq, state, sequenceNum, windowStart, windowEnd, 
          reqNum

(* define statement *)
MIN(x,y)  == IF (x < y) THEN x ELSE y


vars == << sendData, receiveReq, state, sequenceNum, windowStart, windowEnd, 
           reqNum >>

ProcSet == {"send"} \cup {"syn"} \cup {"ack"} \cup {"fin"} \cup {"finack"}

Init == (* Global variables *)
        /\ sendData = <<>>
        /\ receiveReq = <<>>
        /\ state = "opening"
        /\ sequenceNum = 1
        /\ windowStart = 1
        /\ windowEnd = WINDOW_SIZE+1
        /\ reqNum = -1

Send == /\ state = "open" /\ (sendData = <<>> \/ receiveReq # <<>>)
        /\ IF receiveReq # <<>> /\ receiveReq[1] # CORRUPT_DATA
              THEN /\ IF receiveReq[1] = Len(MESSAGES) + 1
                         THEN /\ state' = "SENDING_FIN"
                              /\ UNCHANGED << windowStart, windowEnd >>
                         ELSE /\ IF receiveReq[1] > windowStart
                                    THEN /\ windowEnd' = MIN(WINDOW_SIZE + receiveReq[1], Len(MESSAGES))
                                         /\ windowStart' = receiveReq[1]
                                    ELSE /\ TRUE
                                         /\ UNCHANGED << windowStart, 
                                                         windowEnd >>
                              /\ state' = state
              ELSE /\ TRUE
                   /\ UNCHANGED << state, windowStart, windowEnd >>
        /\ receiveReq' = <<>>
        /\ IF sendData = <<>> /\ MESSAGES # <<>> /\ sequenceNum < Len(MESSAGES) + 1 /\ state' # "closing"
              THEN /\ sendData' = <<sequenceNum, MESSAGES[sequenceNum]>>
                   /\ IF sequenceNum < windowEnd' /\ sequenceNum > windowStart' - 1
                         THEN /\ sequenceNum' = sequenceNum + 1
                         ELSE /\ sequenceNum' = windowStart'
              ELSE /\ TRUE
                   /\ UNCHANGED << sendData, sequenceNum >>
        /\ UNCHANGED reqNum

SYN == /\ state = "opening" /\ sendData = <<>>
       /\ IF receiveReq # <<>>
             THEN /\ IF receiveReq # CORRUPT_DATA
                        THEN /\ IF receiveReq[1] = 1 /\ receiveReq[2] = 1 /\ receiveReq[3] = sequenceNum + 1
                                   THEN /\ reqNum' = receiveReq[4] + 1
                                        /\ state' = "SYN_ACK_RECEIVED"
                                   ELSE /\ TRUE
                                        /\ UNCHANGED << state, reqNum >>
                        ELSE /\ TRUE
                             /\ UNCHANGED << state, reqNum >>
                  /\ receiveReq' = <<>>
             ELSE /\ TRUE
                  /\ UNCHANGED << receiveReq, state, reqNum >>
       /\ IF state' = "opening"
             THEN /\ sendData' = <<1, 0, sequenceNum>>
             ELSE /\ TRUE
                  /\ UNCHANGED sendData
       /\ UNCHANGED << sequenceNum, windowStart, windowEnd >>

ACK == /\ state = "SYN_ACK_RECEIVED"
       /\ IF receiveReq # <<>>
             THEN /\ IF receiveReq # CORRUPT_DATA
                        THEN /\ IF Len(receiveReq) = 1 /\ receiveReq[1] = reqNum -1
                                   THEN /\ state' = "open"
                                        /\ UNCHANGED receiveReq
                                   ELSE /\ receiveReq' = <<>>
                                        /\ state' = state
                        ELSE /\ receiveReq' = <<>>
                             /\ state' = state
             ELSE /\ TRUE
                  /\ UNCHANGED << receiveReq, state >>
       /\ IF state' = "SYN_ACK_RECEIVED"
             THEN /\ sendData' = <<0, 1, sequenceNum + 1, reqNum>>
             ELSE /\ TRUE
                  /\ UNCHANGED sendData
       /\ UNCHANGED << sequenceNum, windowStart, windowEnd, reqNum >>

FIN == /\ state = "SENDING_FIN"
       /\ IF receiveReq # <<>>
             THEN /\ IF receiveReq # CORRUPT_DATA
                        THEN /\ IF receiveReq[1] = -2 /\ receiveReq[2] = "FIN-ACK"
                                   THEN /\ state' = "RECEIVED_FIN-ACK"
                                   ELSE /\ TRUE
                                        /\ state' = state
                        ELSE /\ TRUE
                             /\ state' = state
             ELSE /\ TRUE
                  /\ state' = state
       /\ receiveReq' = <<>>
       /\ IF state' = "SENDING_FIN"
             THEN /\ sendData' = <<-1, "FIN">>
             ELSE /\ TRUE
                  /\ UNCHANGED sendData
       /\ UNCHANGED << sequenceNum, windowStart, windowEnd, reqNum >>

FINACK == /\ (state = "RECEIVED_FIN-ACK" \/ state = "Closed")
          /\ state' = "Closed"
          /\ sendData' = <<-3, "ACK">>
          /\ UNCHANGED << receiveReq, sequenceNum, windowStart, windowEnd, 
                          reqNum >>

Next == Send \/ SYN \/ ACK \/ FIN \/ FINACK

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Send)
        /\ WF_vars(SYN)
        /\ WF_vars(ACK)
        /\ WF_vars(FIN)
        /\ WF_vars(FINACK)

\* END TRANSLATION

\* checks that the message we are trying to send is of the correcdt type
             
WinStrOK == /\ windowStart < Len(MESSAGES) + 1 

WinEndOK == /\ windowEnd < Len(MESSAGES) + 1 
            /\ windowEnd = windowStart + WINDOW_SIZE
            
SeqNumOK == /\ sequenceNum > 0
            /\ sequenceNum > windowStart - 1 
            /\ sequenceNum < windowEnd 
            /\ sequenceNum < Len(MESSAGES) + 1 

Invariants == /\ WinStrOK
              /\ WinEndOK
              /\ SeqNumOK

Properties == \A x \in {"RECEIVED_FIN-ACK", "SYN_ACK_RECEIVED", "open", "opening", "Closed", "SENDING_FIN" }: <>( state = x )
              


\* Both of the below proccesses are weakly fair
Fairness == /\ WF_vars(Send)
            /\ WF_vars(SYN)
            /\ WF_vars(ACK)
            /\ WF_vars(FIN)
            /\ WF_vars(FINACK)
=============================================================================
\* Modification History
\* Last modified Thu Jun 13 02:04:40 NZST 2019 by sdmsi
\* Created Mon Jun 10 00:58:39 NZST 2019 by sdmsi
