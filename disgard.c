#include <stdio.h>
#include <ctype.h>
#include <stdlib.h>
#include <string.h>

#define INOP 0
#define IIX 1
#define IBIT 2
#define IREL 3
#define IJMP 4
#define ICALL 5
#define IRET 6
#define IDATA 7

#define DATA 1
#define HEXD 2
#define BITF 3
#define JUMP 4
#define LOOP 5
#define PROC 6
#define MAIN 7
#define DOVRIDE 8

#define NOTABLE 1
#define NOSOURCE 2

#define NEXTFIELD() while (isspace(*(++line)))
#define HEXNUM(c) (isupper(c) ? c-'A'+10 : (islower(c) ? c-'a'+10 : c-'0'))
#define CHR(b) ((b) >= 32 && (b) <= 126)

typedef unsigned char byte;
typedef signed char sbyte;
typedef unsigned short word;

typedef struct {
        byte opbytes, bytes, type;
        byte op0, op1, mask, masked;
        char mnem[5];
        char args[10];
} instDef;

typedef struct {
        word addr;
        byte type;
        char *name;
} label;

typedef struct {
        word value;
        char *name;
} symbol;

instDef instructions[1000];
int tableSize = 0;

byte *blocks;
label *labels;

word programSize = 0;

word address = 0;

word *relocations, relCnt=0;

symbol symbols[500];
word symbolCnt;

FILE *table, *header, *source, *output;

char *tfile="TASM80.TAB", *hfile="USGARD.H", *sfile, *ofile=NULL;
int final=0, lowercase=0, reloc=1, labeladdr=0, jumptab=0, symbolspan=50;

int header85s;

word zsfuncaddr[11] = {0x8C0C,0x8C0F,0x8C12,0x8C18,0x8C1E,0x8C24,0x8C27,
     0x8C2A,0x8C30,0x8C36,0x8CC8};
char *zsfuncs[11] = {"CALL_Z","CALL_","CALL_NZ","CALL_C","CALL_NC",
     "JUMP_Z","JUMP_","JUMP_NZ","JUMP_C","JUMP_NC","RCALL_"};

char *zsromcalls[14] = {"TX_CHARPUT","D_LT_STR","M_CHARPUT","D_ZM_STR",
     "D_LM_STR","GET_T_CUR","SCROLL_UP","TR_CHARPUT","CLEARLCD","D_HL_DECI",
     "CLEARTEXT","D_ZT_STR","BUSY_OFF","BUSY_ON"};

char *strlwr(char *s)
{
    static char temp[255];
    char *t = temp;
    while (*s)
        *t++ = tolower((unsigned char) *s++);
    *t = 0;
    return temp;
}

word hexword(char *s)
{
       word p;

       p = HEXNUM(*s)*16*256; s++;
       p += HEXNUM(*s)*256; s++;
       p += HEXNUM(*s)*16; s++;
       p += HEXNUM(*s);

       return p;
}

void readInst(int i, char *line)
{
       instDef *p;
       char rule[10];

       p = instructions+i;
       // MNEMONIC
       for (i=0; !isspace(*line); i++)
           p->mnem[i] = *line++;
       p->mnem[i] = 0;
       NEXTFIELD();
       // ARGS
       for (i=0; !isspace(*line); i++)
           p->args[i] = *line++;
       p->args[i] = 0;
       NEXTFIELD();
       // OPCODES
       p->op0 = HEXNUM(*line)*16; line++;
       p->op0 += HEXNUM(*line); line++;
       p->opbytes = 1;
       if (!isspace(*line))
       {
                p->opbytes++;
                p->op1 = p->op0;
                p->op0 = HEXNUM(*line)*16; line++;
                p->op0 += HEXNUM(*line); line++;
       }
       NEXTFIELD();
       // BYTES
       p->bytes = *line++ - '0';
       NEXTFIELD();
       // RULE
       for (i=0; !isspace(*line); i++)
           rule[i] = *line++;
       rule[i] = 0;
       if (!strcmp(rule,"ZIX\0")) p->type = IIX;
       else if (!strcmp(rule,"ZBIT\0")) p->type = IBIT;
       else if (!strcmp(rule,"R1\0")) p->type = IREL;
       else if (!strcmp(p->mnem,"CALL\0")) p->type = ICALL;
       else if (!strcmp(p->mnem,"RETI\0") || !strcmp(p->mnem,"RETN\0") ||
        !strcmp(p->mnem,"JP\0") && !strchr(p->args,',') &&
        (p->args[0] == '(' || !jumptab) ||
        !strcmp(p->mnem,"RET\0") && p->args[0] == '\"')
            p->type = IRET;
       else if (!strcmp(p->mnem,"JP\0")) p->type = IJMP;
       else if (!strcmp(p->mnem,"LD\0") && p->bytes - p->opbytes == 2 &&
            strchr(strchr(p->args,'*')+1,'*') == NULL)
            p->type = IDATA;
       else p->type = INOP;
       NEXTFIELD();
       // CLASS
       if (*(++line) == '\n') { p->mask = p->masked = 0; return; }
       p->masked = 1;
       NEXTFIELD();
       // SHIFT
       line++;
       NEXTFIELD();
       // OR
       p->mask = HEXNUM(*line)*16; line++;
       p->mask += HEXNUM(*line);
}

void error(int type)
{
        switch (type)
        {
        case NOTABLE: printf("Table file not found.\n"); break;
        case NOSOURCE: printf("Source file not found.\n"); break;
        }
        exit(type);
}

void readtable(char *filename)
{
        int i;
        char line[80];

        if ((table = fopen(filename,"r")) == NULL) error(NOTABLE);
        fgets(line,80,table);
        for (i=0; i < 1000; i++)
        {
            do { if (!fgets(line,80,table)) goto tablefinished;
            } while (line[0] && !isalnum(line[0]));
            readInst(i,line);
            tableSize++;
        }
tablefinished:
        fclose(table);
}

int symcmp(const void *elem1,const void *elem2)
{
        if (((symbol *) elem1)->value > ((symbol *) elem2)->value)
           return -1;
        return 1;
}

void readheader(char *filename)
{
        int i;
        char buf[80], *line;

        if ((header = fopen(filename,"r")) == NULL) return;
        symbolCnt = 0;
        while (1)
        {
                if (!fgets(buf,80,header)) break;
                if (!isalnum(buf[0])) continue;
                line = buf;
                symbols[symbolCnt].name = malloc(33);
                for (i=0; i < 32 && !isspace(*line); i++, line++)
                    symbols[symbolCnt].name[i] = *line;
                symbols[symbolCnt].name[i] = 0;
                while (*line++ != '$');
                if (!isalnum(line[2]))
                {
                 free(symbols[symbolCnt].name); continue;
                }
                symbols[symbolCnt++].value = hexword(line);
        }
        fclose(header);
        qsort(symbols,symbolCnt,sizeof (symbol),symcmp);
}

int hasReloc(word addr, instDef *inst)
{
        int i;

        for (i=0; i < relCnt; i++)
            if (relocations[i] == addr+inst->opbytes) return 1;
        return 0;
}

int isSymbol(word arg)
{
        int i;

        for (i=0; i < symbolCnt; i++)
           if (symbols[i].value == arg)
               return 1;
           else if (symbols[i].value < arg &&
              symbols[i].value >= arg-symbolspan)
                return 1;
        return 0;
}

int isZSFunc(word arg)
{
        int i;

        for (i=0; i<11; i++)
            if (zsfuncaddr[i] == arg) return i;
        return -1;
}

label *findLabel(word addr)
{
        int i;

        for (i=0; i < programSize; i++)
            if (labels[i].addr == addr)
               return labels+i;
        return NULL;
}

int addLabel(word addr,byte type)
{
        label *lbl;

        if ((lbl = findLabel(addr)) != NULL && lbl->type < type)
        {  lbl->type = type; return 1; }
        return 0;
}

byte bit_op1;

instDef *findInst(void)
{
        byte op0,op1, flag=0, temp;
        instDef *p;
        static instDef db;
        int i;

        p = instructions;
        if ((i = getc(source)) == EOF) return NULL;
        op0 = i;
        for (i=0; i < tableSize; i++, p++)
            if (p->op0 == op0)
            {
                if (p->opbytes == 1) return p;
                if (!flag) { op1 = getc(source); flag = 1; }
                if (p->type == IBIT && p->bytes == p->opbytes &&
                   p->op1 == (op1&0xC7)) { bit_op1 = op1; return p; }
                if (p->op1 != op1) continue;
                if (!p->masked) return p;
                getc(source);
                temp = getc(source);
                fseek(source,-2,SEEK_CUR);
                if (p->type == IBIT && (temp&0xC7) == p->mask ||
                   temp == p->mask)               return p;
            }
        if (flag) fseek(source,-1,SEEK_CUR);
        db.opbytes = 1; db.bytes = 1; db.type = INOP;
        db.op0 = op0; db.op1 = db.mask = db.masked = 0;
        strcpy(db.mnem,".DB"); sprintf(db.args,"$%02X\t;?Ins",op0);
        return &db;
}

char *decodeByte(byte arg)
{
        static char temp[4];
        snprintf(temp, 4, "%d", arg);
        return temp;
}

char *decodeSByte(sbyte arg)
{
        static char temp[5];

        if (arg == 0) return "";
        temp[0] = (arg < 0) ? '-' : '+';
        snprintf(temp+1, 4, "%d", abs((signed int) arg));
        return temp;
}

char *decodeWord(word arg)
{
        static char temp[40];
        int i;
        label *lbl;

        if ((lbl = findLabel(arg)) != NULL && lbl->type)
           return lbl->name;
        for (i=0; i < symbolCnt; i++)
            if (symbols[i].value == arg)
               return symbols[i].name;
            else if (symbols[i].value < arg &&
              symbols[i].value >= arg-symbolspan)
            {
                sprintf(temp,"%s+%d",symbols[i].name,arg-symbols[i].value);
                return temp;
            }
        sprintf(temp,"$%04X",arg);
        return temp;
}

char *decodeInstr(void)
{
        word arg;
        byte i,flag = 0;
        int j;
        instDef *inst;
        static char result[40];

        inst = findInst();
        arg = 0;
        switch (inst->bytes - inst->opbytes)
        {
        case 1: arg = (byte) getc(source); break;
        case 2: arg = (byte) getc(source);
                arg += ((word) getc(source))*256; break;
        }
        address += inst->bytes;
        strcpy(result,inst->mnem);
        strcat(result,"\t");
        if (lowercase) strlwr(result);
        switch (inst->type)
        {
        case ICALL:
             if (strchr(inst->args,',') == NULL &&
              (j = isZSFunc(arg)) >= 0)
             {
                arg = (byte) getc(source);
                arg += ((word) getc(source))*256;
                sprintf(result,"%s(%s)",zsfuncs[j],decodeWord(arg));
                address += 2;
                break;
             }
             if (arg == 0x8C09)
             {
                if ((arg = (byte) getc(source)) == 0x80)
                    strcpy(result,"ROM_CALL(FIND_PIXEL)");
                else
                    sprintf(result,"ROM_CALL(%s)",zsromcalls[arg]);
                address++;
                break;
             }
        case IJMP:
        case IRET:
        case IDATA:
        case INOP:
             for (i=0; inst->args[i]; i++)
                 if (inst->args[i] == '\"') break;
                 else if (inst->args[i] == '*')
                 {
                      if (hasReloc(address-inst->bytes,inst))
                         strcat(result,"&");
                      if (inst->bytes-inst->opbytes == 2)
                         strcat(result,decodeWord(arg));
                      else
                          strcat(result,decodeByte(arg));
                 }
                 else
                 {
                        result[strlen(result)+1] = 0;
                        result[strlen(result)] = lowercase ?
                         tolower(inst->args[i]) : inst->args[i];
                 }
             break;
        case IIX:
             for (i=0; inst->args[i]; i++)
                 if (inst->args[i] == '*')
                 {
                    if (!flag)
                    {
                     strcat(result,decodeSByte(arg&(255-inst->mask)));
                     arg /= 256; flag = 1;
                    }
                    else strcat(result,decodeByte(arg));
                 }
                 else
                 {
                        result[strlen(result)+1] = 0;
                        result[strlen(result)] = lowercase ?
                         tolower(inst->args[i]) : inst->args[i];
                 }
             break;
        case IBIT:
             if (inst->bytes == inst->opbytes)
                arg = bit_op1;
             else    arg = (arg&255)*256 + (arg/256);
             for (i=0; inst->args[i]; i++)
                 if (inst->args[i] == '*')
                 {
                        if (!flag)
                        {
                         strcat(result,decodeByte((arg&0x38)/8));
                         arg /= 256; flag = 1;
                        }
                        else strcat(result,decodeSByte(arg&255));
                 }
                 else
                 {
                        result[strlen(result)+1] = 0;
                        result[strlen(result)] = lowercase ?
                         tolower(inst->args[i]) : inst->args[i];
                 }
             break;
        case IREL:
             for (i=0; inst->args[i]; i++)
                 if (inst->args[i] == '*')
                    strcat(result,decodeWord(labels[address-2].addr+2+
                     ((sbyte) arg)));
                 else
                 {
                        result[strlen(result)+1] = 0;
                        result[strlen(result)] = lowercase ?
                         tolower(inst->args[i]) : inst->args[i];
                 }
             break;
        }
        return result;
}

void phase1(void)
{
        int i=0,j;
        instDef *inst;
        byte blockend, newrun;
        word literal;

        fseek(source,header85s,SEEK_SET);
        do {if (labels[i++].type) goto loop;
        } while (getc(source) != 0);
        if (!labels[i].type) labels[i].type = MAIN;
loop:
        i = 0;
        newrun = 0;
        while (1)
        {
          while (1)
          {
           if (labels[i].type >= JUMP && labels[i].type < DOVRIDE)
              if (!blocks[i]) break;
           if (blocks[i]) while (blocks[++i]);
           else i++;
           if (i >= programSize) if (newrun) goto loop; else return;
          }
          fseek(source,header85s+i,SEEK_SET);
          blockend = 0;
          do {
             if (blocks[i] || labels[i].type == DOVRIDE) break;
             inst = findInst();
             for (j=0; j < inst->bytes; j++)
                 blocks[i++] = 1;
             switch (inst->type)
             {
             case IRET:
                        blockend = 1;
                        if (strcmp(inst->mnem,"JP\0") ||
                         inst->args[0] == '(') break;
             case IJMP:
                        literal = getc(source);
                        literal += (word) (getc(source)*256);
                        if (!reloc && !isSymbol(literal) ||
                         hasReloc(i-inst->bytes,inst))
                          if (addLabel(literal,JUMP) &&
                           findLabel(literal)-labels < i) newrun=1;
                        break;
             case IREL:
                        literal = labels[i-2].addr+2+(sbyte) getc(source);
                        if (addLabel(literal,(literal <= i) ? LOOP : JUMP)
                         && literal < i)
                           newrun = 1;
                        if (!strcmp(inst->mnem,"JR\0") &&
                         strchr(inst->args,',') == NULL)
                           blockend = 1;
                        break;
             case ICALL:
                       literal = (byte) getc(source);
                       literal += ((word) getc(source))*256;
                       if ((j = isZSFunc(literal)) >= 0)
                       {
                                literal = (byte) getc(source);
                                literal += ((word) getc(source))*256;
                                if (addLabel(literal,(j>=5&&j<=9)?JUMP:PROC)
                                 && findLabel(literal)-labels < i)
                                   newrun = 1;
                                blocks[i] = blocks[i+1] = 1; i += 2;
                                if (j == 6) blockend = 1;
                                break;
                       }
                       if (literal == 0x8C09)
                       {
                                blocks[i++] = 1;
                                break;
                       }
                       if (!reloc && !isSymbol(literal) ||
                        hasReloc(i-inst->bytes,inst))
                         if (addLabel(literal,PROC) &&
                          findLabel(literal)-labels < i) newrun=1;
                       break;
             case IDATA:
                       literal = (byte) getc(source);
                       literal += ((word) getc(source))*256;
                       if (!reloc && !isSymbol(literal)
                        || hasReloc(i-inst->bytes,inst))
                         addLabel(literal,DATA);
             }
             fseek(source,header85s+i,SEEK_SET);
             if (i >= programSize) break;
          } while (!blockend);
        }
}

void phase2(void)
{
        int i = -1, j, bytes;
        word literal;
        instDef *inst;

        while (1)
        {
           while (!blocks[++i]) if (i >= programSize) return;
           while (i < programSize && blocks[i])
           {
                fseek(source,header85s+i,SEEK_SET);
                inst = findInst();
                bytes = inst->bytes;
                if (!strcmp(inst->mnem,"CALL") && inst->args[0] != '(' &&
                 strchr(inst->args,',') == NULL)
                {
                    literal = (byte) getc(source);
                    literal += ((word) getc(source))*256;
                    if (isZSFunc(literal) >= 0) bytes = 5;
                    else if (literal == 0x8C09) bytes = 4;
                }
                for (j=1; j < bytes; j++)
                    if (labels[i+j].type)
                    {
                       if (!labels[i].type) labels[i].type = DATA;
                       labels[i+j].name = (char *) j;
                    }
                i += bytes;
           }
           if (i >= programSize) return;
        }
}

void phase3(void)
{
        int i, j;
        word proc=0, label=0, loop=0, data=0, ins=0;

        for (i=0; i < programSize; i++)
            if (labels[i].type)
            {
              if (labels[i].name != 0)
              {
                 j = (int) labels[i].name;
                 labels[i].name = malloc(32);
                 sprintf(labels[i].name,"%s+%d",
                   labels[i-j].name,j);
                 continue;
              }
              labels[i].name = malloc(32);
              switch (labels[i].type)
              {
              case DOVRIDE:
              case BITF:
              case HEXD:
              case DATA: if (blocks[i])
                         {
                            if (proc==0)
                             sprintf(labels[i].name,"MAIN_ins_%d",ins++);
                            else
                             sprintf(labels[i].name,"P%d_ins_%d",proc,ins++);
                         }
                         else
                             sprintf(labels[i].name,"DATA_%d",data++);
                         break;
              case JUMP: if (proc==0)
                           sprintf(labels[i].name,"MAIN_%d",label++);
                         else
                           sprintf(labels[i].name,"P%d_%d",proc,label++);
                         break;
              case LOOP: if (proc==0)
                           sprintf(labels[i].name,"MAIN_loop_%d",loop++);
                         else
                           sprintf(labels[i].name,"P%d_loop_%d",proc,loop++);
                         break;
              case PROC:
                   sprintf(labels[i].name,"PROC_%d",++proc,label=loop=ins=0);
                   break;
              case MAIN: sprintf(labels[i].name,"MAIN"); break;
              }
            }
}

void phase4(void)
{
        byte c,flip=0, tempc1, tempc2, tempc3;
        word a,i;
        int j, fcnt = 999, mode=0;
        char *disass;

        fseek(source,header85s,SEEK_SET);
        printf("#include \"%s\"\n",lowercase ? strlwr(hfile) : hfile);
        while (address < programSize)
        {
                if (labels[address].type >= PROC &&
                 labels[address].type < DOVRIDE ||
                 blocks[address] && !flip ||
                 labels[address].type && !blocks[address] ||
                 !blocks[address] && flip)
                        printf("\n");
                if (!address ||
                 labels[address].addr != labels[address-1].addr+1)
                        printf(lowercase? "\n.org $%X\n\n":"\n.ORG $%X\n\n",
                         labels[address].addr);
                if (labels[address].type == PROC)
                        printf(";******\n");
                if (labels[address].type)
                {
                        printf("%s:",labels[address].name);
                        if (labeladdr) printf("\t\t\t\t; $%04X",
                                        labels[address].addr);
                        printf("\n");
                }
                a = address;
                if (!final || blocks[a])
                   disass = decodeInstr();
                else
                {
                        c = getc(source);
                        if (flip || labels[a].type) mode = 0;
                        if (flip || fcnt >= 16 || labels[a].type)
                        {
                                printf(lowercase ? ".db\t" : ".DB\t");
                                if (mode)
                                   if (CHR(c)) printf("\"");
                                   else mode = 0;
                                fcnt = 0;
                        }
                        flip = 0;
                        if (CHR(c))
                        {
                            if (!mode && a < programSize-4)
                            {
                                tempc1 = getc(source);
                                tempc2 = getc(source);
                                tempc3 = getc(source);
                            }
                            if (mode || a < programSize-4 &&
                             !blocks[a+1] && !blocks[a+2] &&
                             !blocks[a+3] && CHR(tempc1) &&
                             CHR(tempc2) && CHR(tempc3))
                            {
                                a++;
                                fseek(source,header85s+a,SEEK_SET);
                                if (!mode && fcnt)
                                {
                                        printf("\n");
                                        printf(lowercase? ".db\t" : ".DB\t");
                                        fcnt=0;
                                }
                                if (!mode) printf("\"");
                                mode = 1;
                                if (c == '\'' || c == '\"' || c == '\\')
                                   printf("\\");
                                printf("%c",c);
                                fcnt++;
                                if (fcnt == 16 || blocks[a] || labels[a].type)
                                   printf("\"\n");
                                address = a;
                                continue;
                            }
                        }
                        a++;
                        fseek(source,header85s+a,SEEK_SET);
                        if (mode) printf("\"");
                        if (fcnt) printf(",");
                        mode = 0;
                        printf("%d",c);
                        fcnt++;
                        if (fcnt == 16 || blocks[a] || labels[a].type)
                        printf("\n");
                        address = a;
                        continue;
                }
                if (!blocks[a])
                {
                        flip=0;
                        fseek(source,header85s+a,SEEK_SET);
                        printf(".DB ");
                        i = a;
                        while (1)
                        {
                            c = getc(source);
                            printf("%03d\t\t;=$%02hX",c,c);
                            if (CHR(c)) printf(" =\'%c\'",c);
                            else printf("\t");
                            if (++i >= address) break;
                            if (!blocks[i] && (!labels[i].type ||
                               strchr(labels[i].name,'+')))
                               printf("\n.DB ");
                            else break;
                        }
                        if (i != address)
                        {
                                printf("\n");
                                address = i;
                                continue;
                        }
                }
                else flip=1;
                printf("\t%s",disass);
                if (!final) printf("\t\t\t; @ $%04hX / $%04hX",
                   labels[a].addr,a);
                printf("\n");
        }
        printf(lowercase ? "\n\n.end\n" : "\n\n.END\n");
}

void initSource(char *filename)
{
        word p;

        if ((source = fopen(filename,"rb")) == NULL) error(NOSOURCE);
        fseek(source,0x37,SEEK_SET);
        p = (byte) getc(source);
        p += ((word) getc(source))*256;
        header85s = 0x39+p+7;
        fseek(source,0,SEEK_END);
        programSize = ftell(source)-header85s-3;
        blocks = calloc(programSize,sizeof (byte));
        labels = calloc(programSize,sizeof (label));
        for (p = 0; p < programSize; p++)
            labels[p].addr = p;
}

void findRelocations(void)
{
        word p;
        byte d;
        int i;

        fseek(source,-4,SEEK_END);
        p = (byte) getc(source);
        p += ((word) getc(source))*256;
        if ((relCnt = p) == 0) { programSize -= 2; return; }
        fseek(source,-4,SEEK_CUR);
        p = (byte) getc(source);
        p += ((word) getc(source))*256;
        fseek(source,-2+(signed short) p,SEEK_CUR);
        programSize = ftell(source)-header85s;
        p=0;
        relocations = calloc(relCnt,sizeof (word));
        for (i=0; i < relCnt; i++)
        {
                d = getc(source);
                if (d)
                   p = relocations[i] = p+d;
                else
                {
                    p = (byte) getc(source);
                    p += ((word) getc(source))*256;
                    relocations[i] = p;
                }
        }
}

void usage(void)
{
        printf("Disgard, the TI-85/Usgard disassembler by ah76648@uta.fi - AD 2005.\n");
        printf("\nUsage: DISGARD sourcefile.85s [outputfile.asm] [options]\n");
        printf("Options:\n");
        printf(" -tTablefile\t-> use Tablefile instead of .\\TASM80.TAB\n");
        printf(" -hHeaderfile\t-> read Headerfile instead of .\\USGARD.H\n");
        printf(" -oXXXX/YYYY\t-> assume and write .ORG $XXXX at file position $YYYY\n");
        printf(" -cXXXX\t\t-> assume code block at $XXXX\n");
        printf(" -dXXXX\t\t-> assume data block at $XXXX\n");
        printf(" -f\t\t-> output in final format (omit positions, don't disasm data)\n");
        printf(" -l\t\t-> produce lowercase instructions\n");
        printf(" -sDDD\t\t-> assume header file symbols span DDD bytes forward (def. 50)\n");
        printf(" -n\t\t-> no relocation, liberal labeling (ZShell mode)\n");
        printf(" -a\t\t-> print addresses on label lines\n");
        printf(" -j\t\t-> don't regard JP *:s as endind a code block (jump table mode)\n");
        printf("\nBest results are achieved by running the disassembly first with no\n");
        printf("options (except perhaps -n), checking the output, then running it again\n");
        printf("with -f and necessary -c and -d block declarations.\n");
        printf("\nNote: declare all -o statements in order and before any\n");
        printf("-c/-d statements, or false results may appear.\n");
        exit(0);
}
        

void parsecmdline(int argc,char *argv[])
{
        int i;
        word j, orig;

        if (argc < 2) usage();
        sfile = argv[1];
        initSource(sfile);
        for (i=2; i < argc; i++)
            if (argv[i][0] != '-') ofile = argv[i];
            else switch (tolower(argv[i][1]))
                 {
                 case 't': tfile = argv[i]+2; break;
                 case 'h': hfile = argv[i]+2; break;
                 case 'c': sscanf(argv[i]+2,"%4hx",&j);
                           findLabel(j)->type = JUMP; break;
                 case 'd': sscanf(argv[i]+2,"%4hx",&j);
                           findLabel(j)->type = DOVRIDE;
                           break;
                 case 'o': sscanf(argv[i]+2,"%4hx/%4hx",&orig,&j);
                           orig -= j;
                           for (; j < programSize; j++)
                               labels[j].addr = j+orig;
                           break;
                 case 'f': final = 1; break;
                 case 'l': lowercase = 1; break;
                 case 's': symbolspan = atoi(argv[i]+2); break;
                 case 'n': reloc = 0; break;
                 case 'a': labeladdr = 1; break;
                 case 'j': jumptab = 1; break;
                 }
        if (ofile != NULL)
           freopen(ofile,"w",stdout);
}

int main(int argc, char *argv[])
{
        int i;

        parsecmdline(argc,argv);
        readtable(tfile);
        readheader(hfile);
        if (reloc) findRelocations();
        phase1();
        phase2();
        phase3();
        phase4();
        fclose(source);
        return 0;
}
