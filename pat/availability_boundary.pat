//================================================================
// Formal Verification of Avant-Guard Connection-Migration Mechanism
// under Two Attack Types with Two Independent Attackers
// Tool: PAT Model Checker version 3.5.1
// Admissible Behavior = All, System Abstraction = False
//================================================================
// Constant Definitions
//=============================================================
#define PN 8;
#define KN 5;
#define HN 1;
#define RN 5;
#define MAX_PROXY_STATES 2;

//=============================================================
// Enumerations
//=============================================================
enum{Pkt_Out,Pkt_Out_Relay,Pkt_In,Pkt_In_Report};
enum{SYN,ACK,DATA};
enum{P0,P1,P2,P3,P4,P5,P6,P7};
enum{R0,R1,R2,R3,R4};
enum{K0,K1,K2,K3,K4};
enum{H};
enum{C};
enum{S};

//=============================================================
// Channels 
//=============================================================
channel SC 0;
channel CS 0;
channel HS[PN] 0;         // H_hS: host to switch
channel SH[PN] 0;         // SH_h: switch to host
channel KS[KN] 0;         // K_iS: client to switch
channel SK[KN] 0;         // SK_i: switch to client
channel CHand 0;
channel Cforward 0;
channel SHand 0;
channel Sforward 0;
channel HHand 0;
channel Hforward 0;
channel KHand[KN] 0;
channel Kforward[KN] 0;
channel AHand_Flood 0;
channel AHand_BSat 0;

//=============================================================
// State Tables
//=============================================================
var FlowExistTable[KN][HN]=[0,0,0,0,0];
var FlowTable_S[KN][HN][7]=[0,0,0,0,0,0,R2,
                            0,0,0,0,0,0,R1,
                            0,0,0,0,0,0,R0,
                            0,0,0,0,0,0,R3,
                            0,0,0,0,0,0,R4];
var IPTable[RN][HN]=[K2,K1,K0,K3,K4];
var AccessTable[KN][HN]=[0,0,0,0,0];
var FlowTable_C[KN][HN][2]=[P0,P4,P1,P5,P2,P6,P3,P7,P0,P4];
var ActiveProxyStates=0;
var N=0;

//=============================================================
// Controller
//=============================================================
Controller = (CRecipient|||Cforwarder)||CHandler;

CRecipient = SC?m2.i.m1.SIP.SP.DIP.DP.SEQ->CHand!m2.i.m1.SIP.SP.DIP.DP.SEQ->CRecipient;

CHandler = CHand?m2.i.m1.SIP.SP.DIP.DP.SEQ->CHandler1(m2,i,m1,SIP,SP,DIP,DP,SEQ);CHandler;

CHandler1(m2,i,m1,SIP,SP,DIP,DP,SEQ) =
ifa(m2==Pkt_In && m1==ACK){
    Cforward!Pkt_Out.i.m1.SIP.SP.DIP.DP.SEQ.FlowTable_C[SIP][H][1]->Skip};
ifa(m2==Pkt_In_Report && m1==ACK){
    Cforward!Pkt_Out_Relay.i.m1.SIP.SP.DIP.DP.SEQ->Skip};

Cforwarder = ((Cforward?m.i.m1.SIP.SP.DIP.DP.SEQ.e->CS!m.i.m1.SIP.SP.DIP.DP.SEQ.e->Skip)
             [](Cforward?m.i.m1.SIP.SP.DIP.DP.SEQ->CS!m.i.m1.SIP.SP.DIP.DP.SEQ->Skip));Cforwarder;

//=============================================================
// Switch
//=============================================================
Switch = (SRecipient|||Sforwarder)||SHandler;

SRecipient = (([]i:{0..KN-1} @ KS[i]?m1.SIP.SP.DIP.DP.SEQ->SHand!i.m1.SIP.SP.DIP.DP.SEQ->Skip)
            []([]h:{0..PN-1} @ HS[h]?m1.SIP.SP.DIP.DP.SEQ.m2.SIP1.SP1.DIP1.DP1.SEQ1->SHand!h.m1.SIP.SP.DIP.DP.SEQ.m2.SIP1.SP1.DIP1.DP1.SEQ1->Skip)
            [](CS?m2.i.m1.SIP.SP.DIP.DP.SEQ.e->SHand!C.m2.i.m1.SIP.SP.DIP.DP.SEQ.e->Skip)
            [](CS?m2.i.m1.SIP.SP.DIP.DP.SEQ->SHand!C.m2.i.m1.SIP.SP.DIP.DP.SEQ->Skip));SRecipient;

SHandler = (SHand?i.m1.SIP.SP.DIP.DP.SEQ->SHandler1(i,m1,SIP,SP,DIP,DP,SEQ)
           [](SHand?h.m1.SIP.SP.DIP.DP.SEQ.m2.SIP1.SP1.DIP1.DP1.SEQ1->SHandler2(h,m1,SIP,SP,DIP,DP,SEQ,m2,SIP1,SP1,DIP1,DP1,SEQ1))
           [](SHand?C.m2.i.m1.SIP.SP.DIP.DP.SEQ.e->SHandler3(m2,i,m1,SIP,SP,DIP,DP,SEQ,e))
           [](SHand?C.m2.i.m1.SIP.SP.DIP.DP.SEQ->SHandler4(m2,i,m1,SIP,SP,DIP,DP,SEQ)));SHandler;

SHandler1(i,m1,SIP,SP,DIP,DP,SEQ) =
ifa(m1==SYN && FlowExistTable[SIP][H]==0){
    {AccessTable[SIP][H]=AccessTable[SIP][H]+1;}->
    Sforward!i.ACK.DIP.DP.SIP.SP.SEQ+1.SYN.DIP.DP.SIP.SP.N->Skip};
ifa(m1==ACK && FlowExistTable[SIP][H]==0 && FlowTable_S[SIP][H][2]+1==SEQ && ActiveProxyStates < MAX_PROXY_STATES){
    {AccessTable[SIP][H]=AccessTable[SIP][H]+1;
     ActiveProxyStates = ActiveProxyStates + 1;
     FlowTable_S[SIP][H][0]=DP;
     FlowTable_S[SIP][H][1]=DIP;
     FlowTable_S[SIP][H][2]=SEQ;
     FlowTable_S[SIP][H][3]=N;}->
    Sforward!C.Pkt_In.i.m1.SIP.SP.DIP.DP.SEQ->Skip};
ifa(m1==DATA && FlowExistTable[SIP][H]==1 && ActiveProxyStates > 0){
    Sforward!FlowTable_S[SIP][H][5].DATA.FlowTable_S[SIP][H][6].FlowTable_S[SIP][H][5].DIP.DP.FlowTable_S[SIP][H][2]->
    {FlowTable_S[SIP][H][2]=FlowTable_S[SIP][H][2]+1;
     ActiveProxyStates = ActiveProxyStates - 1;}->Skip}
else{Skip};

SHandler2(h,m1,SIP,SP,DIP,DP,SEQ,m2,SIP1,SP1,DIP1,DP1,SEQ1) =
ifa(m1==ACK && FlowExistTable[IPTable[DIP][H]][H]==0 && m2==SYN){
    Sforward!h.ACK.DIP1.DP1.SIP1.SP1.SEQ1+1->Skip;
    {FlowTable_S[IPTable[DIP][H]][H][4]=SEQ1;}->
    Sforward!C.Pkt_In_Report.h.ACK.DIP1.DP1.SIP1.SP1.SEQ1+1->Skip};

SHandler3(m2,i,m1,SIP,SP,DIP,DP,SEQ,e)=
ifa(m2==Pkt_Out){
    {FlowTable_S[SIP][H][5]=e;}->
    Sforward!e.SYN.FlowTable_S[SIP][H][6].e.DIP.DP.FlowTable_S[SIP][H][2]->Skip};

SHandler4(m2,i,m1,SIP,SP,DIP,DP,SEQ) =
ifa(m2==Pkt_Out_Relay){
    {FlowExistTable[IPTable[SIP][H]][H]=1;}->Skip};

Sforwarder = ((Sforward?h.m1.SIP.SP.DIP.DP.SEQ->SH[h]!m1.SIP.SP.DIP.DP.SEQ->Skip)
             [](Sforward?i.m1.SIP.SP.DIP.DP.SEQ.m2.SIP1.SP1.DIP1.DP1.SEQ1->SK[i]!m1.SIP.SP.DIP.DP.SEQ.m2.SIP1.SP1.DIP1.DP1.SEQ1->Skip)
             [](Sforward?C.m2.i.m1.SIP.SP.DIP.DP.SEQ->SC!m2.i.m1.SIP.SP.DIP.DP.SEQ->Skip));Sforwarder;

//=============================================================
// Client
//=============================================================
Client(x) = (KRecipient(x)|||(Kforwarder(x)|||Kforwarder1(x)))||KHandler(x);

KRecipient(x) = (SK[x]?m1.SIP.SP.DIP.DP.SEQ.m2.SIP1.SP1.DIP1.DP1.SEQ1->KHand[x]!m1.SIP.SP.DIP.DP.SEQ.m2.SIP1.SP1.DIP1.DP1.SEQ1->Skip);KRecipient(x);

KHandler(x) = KHand[x]?m1.SIP.SP.DIP.DP.SEQ.m2.SIP1.SP1.DIP1.DP1.SEQ1->KHandler1(x,m1,SIP,SP,DIP,DP,SEQ,m2,SIP1,SP1,DIP1,DP1,SEQ1);KHandler(x);

KHandler1(x,m1,SIP,SP,DIP,DP,SEQ,m2,SIP1,SP1,DIP1,DP1,SEQ1) =
ifa(m1==ACK && m2==SYN){
    Kforward[x]!ACK.DIP1.DP1.SIP1.SP1.SEQ1+1->Skip;
    Kforward[x]!DATA.DIP1.DP1.SIP1.SP1.SEQ1+1->Skip};

Kforwarder(x)  = KS[x]!SYN.x.P1.H.P0.N->Skip;
Kforwarder1(x) = Kforward[x]?m.SIP.SP.DIP.DP.SEQ->KS[x]!m.SIP.SP.DIP.DP.SEQ->Kforwarder1(x);

//=============================================================
// Host
//=============================================================
Host = (Hforwarder|||HRecipient)||HHandler;

HRecipient = ([]i:{0..PN-1} @ SH[i]?m1.SIP.SP.DIP.DP.SEQ->HHand!i.m1.SIP.SP.DIP.DP.SEQ->Skip);HRecipient;

HHandler = HHand?i.m1.SIP.SP.DIP.DP.SEQ->HHandler1(i,m1,SIP,SP,DIP,DP,SEQ);HHandler;

HHandler1(i,m1,SIP,SP,DIP,DP,SEQ) =
ifa(m1==SYN){
    Hforward!i.ACK.DIP.DP.SIP.SP.SEQ+1.SYN.DIP.DP.SIP.SP.N->Skip};

Hforwarder = Hforward?i.m1.SIP.SP.DIP.DP.SEQ.m2.SIP1.SP1.DIP1.DP1.SEQ1->HS[i]!m1.SIP.SP.DIP.DP.SEQ.m2.SIP1.SP1.DIP1.DP1.SEQ1->Skip;Hforwarder;

//=============================================================
// Attacker 1 (K3): SYN Flood
//=============================================================
Attacker_SYNFlood = (ARecipient_Flood|||Aforwarder_Flood)||AHandler_Flood;

ARecipient_Flood = SK[K3]?m1.SIP.SP.DIP.DP.SEQ.m2.SIP1.SP1.DIP1.DP1.SEQ1->
                   AHand_Flood!m1.SIP.SP.DIP.DP.SEQ.m2.SIP1.SP1.DIP1.DP1.SEQ1->
                   Skip;ARecipient_Flood;

AHandler_Flood = AHand_Flood?m1.SIP.SP.DIP.DP.SEQ.m2.SIP1.SP1.DIP1.DP1.SEQ1->
                 AHandler_Flood;

Aforwarder_Flood   = KS[K3]!SYN.K3.P1.H.P0.N->Aforwarder_Flood_1;
Aforwarder_Flood_1 = KS[K3]!SYN.K3.P1.H.P0.N->Skip;

//=============================================================
// Attacker 2 (K4): Buffer Saturation
//=============================================================
Attacker_BufferSat = (ARecipient_BSat|||Aforwarder_BSat)||AHandler_BSat;

ARecipient_BSat = SK[K4]?m1.SIP.SP.DIP.DP.SEQ.m2.SIP1.SP1.DIP1.DP1.SEQ1->
                  AHand_BSat!m1.SIP.SP.DIP.DP.SEQ.m2.SIP1.SP1.DIP1.DP1.SEQ1->
                  Skip;ARecipient_BSat;

AHandler_BSat = AHand_BSat?m1.SIP.SP.DIP.DP.SEQ.m2.SIP1.SP1.DIP1.DP1.SEQ1->
                AHandler_BSat;

Aforwarder_BSat = KS[K4]!SYN.K4.P1.H.P0.N->KS[K4]!ACK.K4.P1.H.P0.1->Skip;

//=============================================================
// System Definitions
//=============================================================
System_TwoClients_Only  = (|||x:{K0,K1}@Client(x))||Switch||Controller||Host;
SystemK0                = Client(K0)||Switch||Controller||Host;
SystemK1                = Client(K1)||Switch||Controller||Host;
System_SYNFlood_K0      = (Attacker_SYNFlood|||Client(K0))||Switch||Controller||Host;
System_SYNFlood_K1      = (Attacker_SYNFlood|||Client(K1))||Switch||Controller||Host;
System_BufferSat_Two    = (|||x:{K0,K1}@Client(x)|||Attacker_BufferSat)||Switch||Controller||Host;
System_BothAttacks_Two  = (|||x:{K0,K1}@Client(x)|||(Attacker_SYNFlood||Attacker_BufferSat))||Switch||Controller||Host;
SystemAttacker_SYNFlood = Attacker_SYNFlood||Switch||Controller||Host;
SystemBothAttackers     = (Attacker_SYNFlood||Attacker_BufferSat)||Switch||Controller||Host;

//=============================================================
// Assertions 
//=============================================================

// Safety
#define AttackerHasNoFlow FlowExistTable[K3][H] == 0;
#assert SystemAttacker_SYNFlood |= [] AttackerHasNoFlow;

#define SYNFloodHasNoFlow FlowExistTable[K3][H] == 0;
#assert SystemBothAttackers |= [] SYNFloodHasNoFlow;

// Liveness
#define Connection_completion_K0  AccessTable[K0][H] == 2 && FlowExistTable[K0][H] == 1;
#define Connection_completion_K1  AccessTable[K1][H] == 2 && FlowExistTable[K1][H] == 1;
#define Connection_completion_Two AccessTable[K0][H] == 2 && FlowExistTable[K0][H] == 1 &&
                                  AccessTable[K1][H] == 2 && FlowExistTable[K1][H] == 1;

#assert SystemK0               |=<> Connection_completion_K0;
#assert SystemK1               |=<> Connection_completion_K1;
#assert System_TwoClients_Only |=<> Connection_completion_Two;
#assert System_SYNFlood_K0     |=<> Connection_completion_K0;
#assert System_SYNFlood_K1     |=<> Connection_completion_K1;
#assert System_BufferSat_Two   |=<> Connection_completion_Two;
#assert System_BothAttacks_Two |=<> Connection_completion_Two;
