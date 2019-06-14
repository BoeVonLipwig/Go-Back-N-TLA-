--------------------------- MODULE Ass3SinclaShau ---------------------------
EXTENDS Naturals, Integers, TLC, Sequences, Bags, FiniteSets
\* the following are to be set in model
CONSTANT  CORRUPT_DATA,
          WINDOW_SIZE,
          MESSAGES(*is the input message to send*), 
          MESSAGE_TYPES(*used to typecheck that the message of the right type*)  

VARIABLES sendDataQueue,   \* send data  to dataWire
          receiveDataQueue,\* receive data and handshake parts from the dataWir
          receiveReqQueue, \* receive data requests and handshake parts from the reqWir 
          sendReqQueue,    \* send data requests and handshake parts to the reqWir
          requestNum,      \* is the index of the packet currently being requested by the recevier
          sequenceNum,     \* is the index of the packet currently being sent by the sender
          windowStart,     \* is the start of the sliding window, will update as more data is sent
          windowEnd,       \* is the end of the sliding window(windowStart + WINDOW_SIZE)
          messOut,         \* is the final output of reciver, the place it puts the data it recives. this is used to check that the right answer has been recived
          senderState,     \* state the sender is currently in (sending SYN or sending data etc)
          receieverState,  \* state the reciver is currently in (sending FIN-ACK or receving data etc)
          synNum,          \* a storage variable used during the 3 way handshake to pair sender and reciver
          reqNum           \* a storage variable used during the 3 way handshake to pair sender and reciver
           
          
          
\* list of all vars
vars == <<sendDataQueue, receiveDataQueue, receiveReqQueue, sendReqQueue, requestNum, sequenceNum, windowStart, windowEnd, messOut, senderState, receieverState, synNum, reqNum>>

\* istanciating the two wires and both the sender and recevier
dataWir == INSTANCE DataWire WITH inputW <- sendDataQueue, outputW <- receiveDataQueue
reqWir == INSTANCE DataWire WITH inputW <- sendReqQueue, outputW <- receiveReqQueue
sender == INSTANCE Sender WITH sendData <- sendDataQueue, receiveReq <- receiveReqQueue, state <- senderState
receiver == INSTANCE Receiver WITH sendReq <- sendReqQueue, receiveData <- receiveDataQueue, output <- messOut, state <- receieverState

 
\* The following varibles run the init code in their respective modules
Init ==  /\ dataWir!Init
         /\ reqWir!Init
         /\ sender!Init
         /\ receiver!Init


\* These are used to help define what the "next" step is and state what variables remain unchanged
dataChannel ==  /\  dataWir!Next
                /\  UNCHANGED <<receiveReqQueue, sendReqQueue, requestNum, sequenceNum, windowStart, windowEnd, messOut, senderState, receieverState, synNum, reqNum>>

reqChannel ==  /\  reqWir!Next
               /\  UNCHANGED <<sendDataQueue, receiveDataQueue, requestNum, sequenceNum, windowStart, windowEnd, messOut, senderState, receieverState, synNum, reqNum>>

senderChannel ==   /\  sender!Next
                   /\  UNCHANGED <<receiveDataQueue, sendReqQueue, requestNum, messOut, receieverState, synNum>>

receiverChannel == /\  receiver!Next
                  /\  UNCHANGED <<sendDataQueue, receiveReqQueue, sequenceNum, windowStart, windowEnd, senderState, reqNum>>
                  
------------------------------------   
\* defines the next step of the algorithim as being the next step of any one of these
Next ==  \/ dataChannel 
         \/ reqChannel
         \/ senderChannel
         \/ receiverChannel
         
(* The following lines inforce the fairness properties of the modules.
   This means that for each of these modules the defined proccess within 
   that have been flaged as either strong or weak fairness will eventually 
   be run *)   
Fairness == /\ sender!Fairness
            /\ receiver!Fairness
            /\ dataWir!Fairness
            /\ reqWir!Fairness
            
(* The following line inforce the invariants of the modules. This is used 
   for type checking *)
Invariants ==  /\ sender!Invariants
               /\ receiver!Invariants
               /\ WINDOW_SIZE < Len(MESSAGES)

Spec == /\ Init /\ [][Next]_vars
        /\ SF_vars(dataChannel /\ Len(receiveDataQueue') = 2  /\ receiveDataQueue'[1] = requestNum)
        /\ Fairness
        /\ Invariants

---------
\* This is used to check that the final output matches the orignal input
\* make sure to add "Properties" in the modules properties tab
CorrectResult == <>(messOut = MESSAGES) /\ <>(senderState = "Closed") /\ <>(receieverState= "Closed")

\*The properties that must be TRUE for the spec to pass and be considered correct
Properties == /\CorrectResult
              /\sender!Properties
              /\receiver!Properties

-------------       

(*
     * I did parts A & B
     * Copied over the entieraty of data wire from abp 
     * Most of the structure for this main control module was copied from my abp
     * The sequenceNum and reciverNum variables always start at 1 
     * Sender :
        * Started from scratch
        * Created a seperate process for each segment of the 3 way connection handshake 
          and controled what one ran using a state variable 
     * Recevier:
        * Started from scratch
        * Created a seperate process for each segment of the 3 way connection handshake and controled what one ran using a state variable
     
     * The whole Spec works as following:
        * Connects via a 3 way hand shake:
            * SYN and ACK are represented as bits insted of text because using text causes issue where text is
              accdently compared to intgers and tla is unable to handle that and checking types before comparinging 
              is difficult and comparitivly costly 
            * Sender send SYN and its ISN (1, 0, SequenceNum)
            * Reciver checks SYN message and replys with SYN ACK Senders ISN + 1 and its own ISN (1, 1, sequencesNumn + 1, reciverNum)
            * Sender replys with ACK and Both ISNs + 1 (0, 1, sequenceNum +1, ReciverNum + 1)
            * Reciver spams a request for data until it recives some and then goes into its reciver state
            * Sender starts waiting for data requests and once it recives one moves into its sending state
            * Both set their state to open
        * Send and recive using the sliding window protocol 
        * Terminate via another 3 way hand shake
            * FIN and ACK are represented as negitive numbers insted of text because using text causes issue where text is
              accdently compared to intgers and tla is unable to handle that and checking types before comparinging 
              is difficult and comparitivly costly.
            * I used negitive numbers insted of bits because if i used the bits solution it would be read as a normal
              message by the reciver as it uses the fist index of the message as the sequence number which is capable of being 1. 
            * Once the sender has recived confimation of its last message being recived it will send a FIN message 
              to state its intention to break to connection, This message is a -1 as sending text causes issues as stated earlier
            * Receiver will recive the -1 and acknolage it with a -2 (representing FIN ACK in this case)
            * Sender will then reply with -3 (Meaning ACK) and reciver upon reciving it will shut off
            * sender has no way to know if the message has been recived by the sender and no way to time out which is the normal
              way to solve this problem so it will just send ACK untilll the end of time after setting its state to closed and which ends the spec
     
*)

=============================================================================
\* Modification History
\* Last modified Fri Jun 14 19:01:59 NZST 2019 by sdmsi
\* Created Fri Jun 07 00:33:58 NZST 2019 by sdmsi
