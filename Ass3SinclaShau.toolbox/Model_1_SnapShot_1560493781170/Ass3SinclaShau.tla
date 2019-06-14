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
     * Sender :
        * Started from scratch
        * Created a seperate process for each segment of the 3 way connection handshake 
          and controled what one ran using a state variable 
        * When the state of the connection was "open" the main sliding window process 
          from part a ran until it had sent its entire set of messages and recived confirmation of them being recived
        * 
     * Recevier:
        * Started from scratch
        * Created a seperate process for each segment of the 3 way connection handshake and controled what one ran using a state variable
        * 
*)

=============================================================================
\* Modification History
\* Last modified Fri Jun 14 18:28:54 NZST 2019 by sdmsi
\* Created Fri Jun 07 00:33:58 NZST 2019 by sdmsi
