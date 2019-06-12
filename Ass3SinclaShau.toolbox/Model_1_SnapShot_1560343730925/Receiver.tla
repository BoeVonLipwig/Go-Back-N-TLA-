------------------------------ MODULE Receiver ------------------------------
EXTENDS Naturals, Integers, TLC, Sequences, Bags, FiniteSets

CONSTANT CORRUPT_DATA, WINDOW_SIZE, MESSAGES, MESSAGE_TYPES
(* --algorithm reciver
variables sendReq = <<>>, receiveData = <<>>, requestNum = 1, output = <<>>, state = "ready", synNum = -1;
fair process Receive = "receive"
begin
A:
    while TRUE do
        await receiveData # <<>> /\ state = "open";
        if receiveData[1] # CORRUPT_DATA then
            \* sender will send -1 if it wants to close the connection
            if receiveData[1] = -1 then
                state := "closing";
            end if;
            if (receiveData[1] = requestNum) then
                output := output \o <<receiveData[2]>>;
                requestNum := requestNum + 1;
            end if;
            sendReq := <<requestNum>>;
        end if;
        receiveData := <<>>;
    end while;
    
end process;

fair process WaitSYN = "waitsyn"
begin
A:
    while TRUE do
        await state = "ready" /\ receiveData # <<>>;
        if receiveData # CORRUPT_DATA then 
            if receiveData[1] = 1 /\ receiveData[2] = 0 then 
                synNum := receiveData[3] + 1;
                state := "SYN-RECIVED";
            else 
                receiveData := <<>>;
            end if;
        else 
            receiveData := <<>>;
        end if;
    end while;
end process;

fair process SendSYNACK = "sendsyn-ack"
begin
A:
    while TRUE do
        await state = "SYN-RECIVED" /\ receiveData # <<>>;
        if receiveData # CORRUPT_DATA then
            if Len(receiveData) = 4 /\ receiveData[1] = 0 /\ receiveData[2] = 1 /\ receiveData[3] = synNum /\ receiveData[4] = requestNum + 1 then
                state := "WAIT-FOR-DATA";
            end if;
            receiveData := <<>>;
        else 
            receiveData := <<>>;
        end if;
        
        if state = "SYN-RECIVED" then
            sendReq := <<1, 1, synNum, requestNum>>;
        end if;
    end while;
end process;

fair process WaitData = "waitdata"
begin 
A: 
    while TRUE do
        await receiveData # <<>> /\ state = "WAIT-FOR-DATA";
        if receiveData # CORRUPT_DATA then 
            if receiveData[1] = requestNum then
                state := "open";
            end if;
        end if;
        if state = "WAIT-FOR-DATA" then 
            sendReq := <<requestNum>>;
            receiveData := <<>>;
        end if
    end while;
end process;

fair process SendFIN = "sendfin"
begin
A: 
    while TRUE do
        
        await receiveData # <<>> /\ state = "closing";
        if receiveData # CORRUPT_DATA then 
            if receiveData[1] = "FIN-ACK" then
                state := "ACK";
            end if;
        end if;
        
        
        if state = "closing" then 
            sendReq := <<"FIN">>;
        end if;
    end while;

end process;

fair process SendACK = "sendack"
begin
A: 
    while TRUE do
        await state = "closing" \/ state = "closed";
        (* since we cant prove this message has been recived by the sender and we cant time this out 
           we will just send it forever as tla does not allow us to fully implement tcp*)
        state := "closed";
        sendReq := <<"ACK">>;
    end while;

end process;
end algorithm; 
*)
\* BEGIN TRANSLATION
\* Label A of process Receive at line 10 col 5 changed to A_
\* Label A of process WaitSYN at line 31 col 5 changed to A_W
\* Label A of process SendSYNACK at line 49 col 5 changed to A_S
\* Label A of process WaitData at line 69 col 5 changed to A_Wa
\* Label A of process SendFIN at line 86 col 5 changed to A_Se
VARIABLES sendReq, receiveData, requestNum, output, state, synNum

vars == << sendReq, receiveData, requestNum, output, state, synNum >>

ProcSet == {"receive"} \cup {"waitsyn"} \cup {"sendsyn-ack"} \cup {"waitdata"} \cup {"sendfin"} \cup {"sendack"}

Init == (* Global variables *)
        /\ sendReq = <<>>
        /\ receiveData = <<>>
        /\ requestNum = 1
        /\ output = <<>>
        /\ state = "ready"
        /\ synNum = -1

Receive == /\ receiveData # <<>> /\ state = "open"
           /\ IF receiveData[1] # CORRUPT_DATA
                 THEN /\ IF receiveData[1] = -1
                            THEN /\ state' = "closing"
                            ELSE /\ TRUE
                                 /\ state' = state
                      /\ IF (receiveData[1] = requestNum)
                            THEN /\ output' = output \o <<receiveData[2]>>
                                 /\ requestNum' = requestNum + 1
                            ELSE /\ TRUE
                                 /\ UNCHANGED << requestNum, output >>
                      /\ sendReq' = <<requestNum'>>
                 ELSE /\ TRUE
                      /\ UNCHANGED << sendReq, requestNum, output, state >>
           /\ receiveData' = <<>>
           /\ UNCHANGED synNum

WaitSYN == /\ state = "ready" /\ receiveData # <<>>
           /\ IF receiveData # CORRUPT_DATA
                 THEN /\ IF receiveData[1] = 1 /\ receiveData[2] = 0
                            THEN /\ synNum' = receiveData[3] + 1
                                 /\ state' = "SYN-RECIVED"
                                 /\ UNCHANGED receiveData
                            ELSE /\ receiveData' = <<>>
                                 /\ UNCHANGED << state, synNum >>
                 ELSE /\ receiveData' = <<>>
                      /\ UNCHANGED << state, synNum >>
           /\ UNCHANGED << sendReq, requestNum, output >>

SendSYNACK == /\ state = "SYN-RECIVED" /\ receiveData # <<>>
              /\ IF receiveData # CORRUPT_DATA
                    THEN /\ IF Len(receiveData) = 4 /\ receiveData[1] = 0 /\ receiveData[2] = 1 /\ receiveData[3] = synNum /\ receiveData[4] = requestNum + 1
                               THEN /\ state' = "WAIT-FOR-DATA"
                               ELSE /\ TRUE
                                    /\ state' = state
                         /\ receiveData' = <<>>
                    ELSE /\ receiveData' = <<>>
                         /\ state' = state
              /\ IF state' = "SYN-RECIVED"
                    THEN /\ sendReq' = <<1, 1, synNum, requestNum>>
                    ELSE /\ TRUE
                         /\ UNCHANGED sendReq
              /\ UNCHANGED << requestNum, output, synNum >>

WaitData == /\ receiveData # <<>> /\ state = "WAIT-FOR-DATA"
            /\ IF receiveData # CORRUPT_DATA
                  THEN /\ IF receiveData[1] = requestNum
                             THEN /\ state' = "open"
                             ELSE /\ TRUE
                                  /\ state' = state
                  ELSE /\ TRUE
                       /\ state' = state
            /\ IF state' = "WAIT-FOR-DATA"
                  THEN /\ sendReq' = <<requestNum>>
                       /\ receiveData' = <<>>
                  ELSE /\ TRUE
                       /\ UNCHANGED << sendReq, receiveData >>
            /\ UNCHANGED << requestNum, output, synNum >>

SendFIN == /\ receiveData # <<>> /\ state = "closing"
           /\ IF receiveData # CORRUPT_DATA
                 THEN /\ IF receiveData[1] = "FIN-ACK"
                            THEN /\ state' = "ACK"
                            ELSE /\ TRUE
                                 /\ state' = state
                 ELSE /\ TRUE
                      /\ state' = state
           /\ IF state' = "closing"
                 THEN /\ sendReq' = <<"FIN">>
                 ELSE /\ TRUE
                      /\ UNCHANGED sendReq
           /\ UNCHANGED << receiveData, requestNum, output, synNum >>

SendACK == /\ state = "closing" \/ state = "closed"
           /\ state' = "closed"
           /\ sendReq' = <<"ACK">>
           /\ UNCHANGED << receiveData, requestNum, output, synNum >>

Next == Receive \/ WaitSYN \/ SendSYNACK \/ WaitData \/ SendFIN \/ SendACK

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Receive)
        /\ WF_vars(WaitSYN)
        /\ WF_vars(SendSYNACK)
        /\ WF_vars(WaitData)
        /\ WF_vars(SendFIN)
        /\ WF_vars(SendACK)

\* END TRANSLATION
\* Checks that all variables remain in valid states

\*TypeOK == /\ \/ output = <<>>
\*             \/ \A i \in DOMAIN output : output[i] \in MESSAGE_TYPES
\*          /\ receiveData = <<>>
\*             \/ \A i \in DOMAIN receiveData : receiveData[i] \in MESSAGE_TYPES

          
          
Invariants == \*/\ TypeOK
              /\ requestNum < Len(MESSAGES)
              /\ requestNum > 0

Fairness == /\ WF_vars(Receive)
            /\ WF_vars(WaitSYN)
            /\ WF_vars(SendSYNACK)
            /\ WF_vars(WaitData)
            /\ WF_vars(SendFIN)
            /\ WF_vars(SendACK)
            
            
            
Properties == \A x \in {"closed", "closing","SYN-RECIVED", "WAIT-FOR-DATA", "open", "ready"}: <>( state = x )

=============================================================================
\* Modification History
\* Last modified Thu Jun 13 00:46:16 NZST 2019 by sdmsi
\* Created Mon Jun 10 00:58:49 NZST 2019 by sdmsi
