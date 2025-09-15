/*
EDX Spelling Checker for Windows
Written by David Deley (Windows version: March 2004)
(Updated 11/03/2006 to properly handle characters above ASCII 127. See "UPDATES" below.)
(Updated 11/19/2006 to properly handle a few more characters above ASCII 127.)
(Updated 11/23/2006 added User's personal Aux1 dictionary support)
http://members.cox.net/deleyd/
If you use my code please give me credit for it. That's all I ask for.

This DLL provides three functions:
1. edx$dic_lookup_word - lookup a word in the lexical database
2. edx$spell_guess     - guess what word the user meant to type
3. edx$dll_version     - just returns the version number of this DLL

HISTORY:

March 1990 - Original spelling checker code written from scratch in VAX
Macro Assembly Language for the EDX text editor I wrote in TPU for VMS
operating systems.

July 1993 - Forced to convert the code to the C language as VAX Macro
became obsolete.

March 2004 - Converted the C code to work on Microsoft Windows so I
could add a spelling checker to the Multi-Edit text & code editor
See: www.multieditsoftware.com (A supurb text and code editor!)
See: http://www.multieditsoftware.com/forums/viewtopic.php?t=473
Tested on Windows XP, Windows 2000, and Windows ME.

July 2006 - Submitted code to www.codeproject.com . I've been using
this spelling checker code on Windows for two years now with no
problems. The code is stable, and fast!

 UPDATES:
11/03/2006
Discovered a problem working with characters above 127.
Here's the real problem I was unaware of, as explained by
Kernighan & Ritchie (whom you probably know as K&R, the
inventors of the language):

"There is one subtle point about the conversion of characters to
integers. The language does not specify whether variables of type
char are signed or unsigned quantities. When a char is converted
to an int, can it ever produce a negative result? The answer varies
from machine to machine, reflecting differences in architecture.
On some machines a char whose leftmost bit is 1 will be converted
to a negative integer ("sign extension"). On others, a char is
promoted to an int by adding zeros at the left end, and thus is
always positive."
--Kernighan & Ritchie: "The C Programming Language"

So I have to be a bit careful to cast as unsigned before I compare.

So I made ANSItolower, as the regular tolower doesn't work on characters above 127.
For ANSItolower I assume we are using the ANSI character set. See file
"EDX_lowercasing_extended_letters.htm" for an explanation of what gets lowercased.

I also defined a new 'flags' field in the database header, with low bit 0
being "Extended_ANSI_Guessing". The EDXBuildDictionary will set this bit
if it encounters a word containing a character above 127. The EDX dictionary
version is now version 5; however, edxspell.dll is backwards compatible with
older version 4 lexical databases which do not have the 'flags' field. Version
4 databases do not support extended characters above 127.

If the Extended_ANSI_Guessing bit is TRUE, spell guessing will use
those extended vowel characters with accents in spell guessing.
Characters such as ß à á â ã ä å æ ç è é ê ë ì í î ï ð ñ ò ó ô õ ö ø ù ú û ü ý þ ÿ


Maybe someday in the future we'll make a version that does UNICODE


11/23/06
 Added support for a user's personal Aux1 dictionary. This is a plain text file
 with one word per line. The file is read into memory when the EDX dictionary
 is loaded.
 There is also a function that will append a new word to the user's personal
 Aux1 dictionary.
*/
/******************************************************************************/
#include "stdafx.h"
#include <windows.h>
#include <string.h>
#include <stdio.h>
#include <ctype.h>
#include <stdlib.h>
//Note: This EDX Spelling Checker VERSION 7.1 November 19, 2006 supports
//      EDX lexical database versions 4 & 5. The EDX lexical database
//      version number is the very first byte of the database, followed
//      by "EDXdict".
//      Version 5 lexical databases support extended characters above 127,
//      and the flags bit 'Extended_ANSI_Guessing' will be set if there
//      are any words in the database with characters above 127. This will
//      cause spell guessing here to included extended ANSI characters
//      when spell guessing.
//Extended ANSI characters
#define  A_WITH_GRAVE          224
#define  A_WITH_ACUTE          225
#define  A_WITH_CIRCUMFLEX     226
#define  A_WITH_TILDE          227
#define  A_WITH_DIAERESIS      228
#define  A_WITH_RING_ABOVE     229
#define  AE                    230
#define  C_WITH_CEDILLA        231
#define  E_WITH_GRAVE          232
#define  E_WITH_ACUTE          233
#define  E_WITH_CIRCUMFLEX     234
#define  E_WITH_DIAERESIS      235
#define  I_WITH_GRAVE          236
#define  I_WITH_ACUTE          237
#define  I_WITH_CIRCUMFLEX     238
#define  I_WITH_DIAERESIS      239
#define  ETH                   240
#define  N_WITH_TILDE          241
#define  O_WITH_GRAVE          242
#define  O_WITH_ACUTE          243
#define  O_WITH_CIRCUMFLEX     244
#define  O_WITH_TILDE          245
#define  O_WITH_DIAERESIS      246
//#define (this is the division sign) 247
#define  O_WITH_STROKE         248
#define  U_WITH_GRAVE          249
#define  U_WITH_ACUTE          250
#define  U_WITH_CIRCUMFLEX     251
#define  U_WITH_DIAERESIS      252
#define  Y_WITH_ACUTE          253
#define  THORN                 254
#define  Y_WITH_DIAERESIS      255

#define SPACE 0x20              /* ASCII space character */
#define EDX__WORDFOUND 1
#define EDX__WORDNOTFOUND 2
#define EDX__ERROR 4
#define ERRMSGLEN 400
#define GUSREV  1               /* 1 = GUESS REVERSALS */
#define GUSVOL  2               /* 2 = GUESS VOWELS */
#define GUSMIN  3               /* 3 = GUESS MINUS */
#define GUSPLS  4               /* 4 = GUESS PLUS */
#define GUSCON  5               /* 5 = GUESS CONSONANTS */
#define GIVEUP  6               /* 6 = GIVE UP */
static BOOL   dic_loaded = FALSE; /* TRUE when EDX dictionary successfully loaded */
static BOOL   Extended_ANSI_Guessing; /* TRUE when EDX dictionary contains extended ANSI characters */
static HANDLE hDicFile = 0;       //Handle to EDX dictionary file
static DWORD  dwDicFileSize;      //Length of EDX dictionary file. Used for mapping file.
static HANDLE hDicFileMap = 0;    // handle for the EDX dictionary file's memory map
static LPVOID lpDicMapBase = 0;   // pointer to the base address of the memory-mapped region
static DWORD target_word_len;     /* length of target word */
static DWORD gmode;               /* guess mode */
static DWORD gof;                 /* guess offset */
static DWORD gsubmode;            /* guess submode */
static DWORD dic_lwl;             /* length of spell word in dic_lwa to check */
#define MAXWORDLEN 31             /* maximum word length dictionary can store is 31 characters */
static unsigned char dic_lwa[MAXWORDLEN+2];/* word spelling checker is currently checking */

#define int32 DWORD
static struct dichead_layout {
   unsigned char id[8];              /* header id */
   int32 lexofst;   /* Offset to beginning of Lexical Database (dictionary page 0) */
   int32 lexlen;    /* Lexical Database Length (in bytes) */
   int32 indofst;   /* Index Length (in bytes) */
   int32 nidxwds;   /* Number of index guide words */
   int32 indswd;    /* Size of each guide Word (in bytes) */
   int32 dicpln;    /* Dictionary Page Length (in bytes) */
   int32 cwdofst;   /* Offset to beginning of Commonwords */
   int32 cwdlen;    /* Commonwords Length (in bytes) */
   int32 cwdmln;    /* Commonwords Maximum Length (in bytes) */
   int32 flags;     /* Low bit set if extended ANSI characters are in the dictionary */
}*dichead;
#define HEADER_LEN  sizeof(dichead_layout)    /* Length of dictionary header */

//User's personal Aux1 dictionary
unsigned char* aux1base = NULL;
unsigned char* aux1ptr = NULL;
#define FNAMESIZE 260
static char Aux1File[FNAMESIZE] = "";

// MACROS
#define LOAD_EIPE_ERROR_MESSAGE \
_snprintf(errbuf, errbuflen, "EDXspell.dll encountered error EXCEPTION_IN_PAGE_ERROR. \
This error can occur if the EDX dictionary file is on a remote computer \
and the network connection to that remote computer is lost.");\
errbuf[errbuflen-1] = '\0';

// Anything ASCII 32 or below will be considered a word delimiter, because the
// design specifies that words can not contain characters 32 or below.
// (This macro does not get used here in edxspell.cpp . It does get used in EDXBuildDictionary.cpp)
#define EDXisspace(c)  ( ((c) <= 32 ) ? TRUE : FALSE )

//ISVOWEL. If char (c) is a vowel
#define ISVOWEL(c) \
         (   ((c) == (unsigned char)'a') \
          || ((c) == (unsigned char)'e') \
          || ((c) == (unsigned char)'i') \
          || ((c) == (unsigned char)'o') \
          || ((c) == (unsigned char)'u') \
          || ((Extended_ANSI_Guessing) && \
              ((c) >= 224 && (c) <= 252 \
                && (c) != 231 \
                && (c) != 240 \
                && (c) != 241 \
                && (c) != 247) \
             ) \
         )


// See file "EDX_lowercasing_extended_letters.htm" for an explanation of what gets lowercased.
//#define ANSItolower(c) ( ( ((c) >= 'A' && (c) <= 'Z') || ( ((c) >= 192) && ((c) <= 222) && ((c) != 215)) )  ? ((c)+0x20) : (c) )
unsigned char ANSItolower(unsigned char c)
{
    if ( ((c >= 65) && (c <= 90)) || ( (c >= 192) && (c <= 222) && (c != 215) ) )
      return( (unsigned char)(c+0x20) );
    else if ((c == 138) || (c == 140) || (c == 142))  //S WITH CARON; LIGATURE OE; Z WITH CARON
      return( (unsigned char)(c+0x10) );
    else if (c == 159)                 //LATIN CAPITAL LETTER Y WITH DIAERESIS
      return( (unsigned char)(255) );  //LATIN SMALL LETTER Y WITH DIAERESIS
    else
      return( (unsigned char)(c) );    //LATIN SMALL LETTER Y WITH DIAERESIS
}

/******************************************************************************/
BOOL WINAPI DllMain(
    HINSTANCE hinstDLL,  // handle to DLL module
    DWORD fdwReason,     // reason for calling function
    LPVOID lpReserved )  // reserved
{
    // Perform actions based on the reason for calling.
    switch( fdwReason )
    {
        case DLL_PROCESS_ATTACH:
         // Initialize once for each new process.
         // Return FALSE to fail DLL load.
            break;

        case DLL_THREAD_ATTACH:
         // Do thread-specific initialization.
            break;

        case DLL_THREAD_DETACH:
         // Do thread-specific cleanup.
            break;

        case DLL_PROCESS_DETACH:
         // Perform any necessary cleanup.
            /* Although an application may close the file handle used to create a file
            mapping object, the system holds the corresponding file open until the last
            view of the file is unmapped. Files for which the last view has not yet been
            unmapped are held open with no sharing restrictions. To fully close a file
            mapping object, an application must unmap all mapped views of the file
            mapping object by calling UnmapViewOfFile, and then close the file mapping
            object handle by calling CloseHandle. */

            if (aux1base)     { delete[] aux1base; }  // User's personal Aux1 dictionary in memory
            if (lpDicMapBase) { UnmapViewOfFile(lpDicMapBase); }
            if (hDicFileMap)  { CloseHandle(hDicFileMap); }
            if (hDicFile)     { CloseHandle(hDicFile); }
            break;
    }
    return TRUE;  // Successful DLL_PROCESS_ATTACH.
}
/******************************************************************************/
void FetchErrorText(DWORD dwErrCode, char *errmsg, char *errbuf, int errbuflen)
{
    LPTSTR lpMessage;
    if (errbuflen < 1) {return;} //errbuflen may be zero
    FormatMessage(FORMAT_MESSAGE_ALLOCATE_BUFFER | FORMAT_MESSAGE_FROM_SYSTEM,
                  NULL, // no source buffer needed
                  dwErrCode, // error code for this message
                  NULL, // default language ID
                  (LPTSTR)&lpMessage, // allocated by fcn
                  NULL, // minimum size of buffer
                  NULL); // no inserts
    _snprintf(errbuf, errbuflen, "%s\n Error is: %u: %s", errmsg, dwErrCode, lpMessage );  //possible buffer overflow here too
    errbuf[errbuflen-1] = '\0';
    return;
}
/******************************************************************************/
//SPELL_INIT           !Initialize spelling checker
//LOAD_MAIN_DIC
//LOAD_AUX1_DIC
BOOL load_main_dic(char *Dic_File_Name, char *errbuf, int errbuflen)
{
  // MAKE SURE WE WERE PASSED A Dic_File_Name.
  if ( !strlen(Dic_File_Name) )
  {
    char errmsg[ERRMSGLEN];
    _snprintf(errmsg, ERRMSGLEN, "Error opening EDX dictionary file.\n No Dic_File_Name passsed.\n Did you call edx$spell_guess before calling edx$dic_lookup_word?\n");
    errmsg[ERRMSGLEN-1] = '\0';
    return(FALSE);
  }

  //OPEN MAIN EDX DICTIONARY FILE
  hDicFile = CreateFile (Dic_File_Name,
                         GENERIC_READ,
                         FILE_SHARE_READ,
                         NULL,
                         OPEN_EXISTING,
                         0,
                         NULL);
  if (hDicFile == INVALID_HANDLE_VALUE)
  {
    DWORD dwErrCode = GetLastError();
    char errmsg[ERRMSGLEN];
    _snprintf(errmsg, ERRMSGLEN, "Error opening %s", Dic_File_Name );
    errmsg[ERRMSGLEN-1] = '\0';
    FetchErrorText(dwErrCode, errmsg, errbuf, errbuflen );
    return(FALSE);
  }

  //GET SIZE OF DICTIONARY FILE
  dwDicFileSize = GetFileSize(hDicFile, NULL);
  if (dwDicFileSize == 0xFFFFFFFF)
  {
    DWORD dwErrCode = GetLastError();
    if (dwErrCode != NO_ERROR)
    {
       char errmsg[ERRMSGLEN];
       _snprintf(errmsg, ERRMSGLEN, "Call to 'GetFileSize' failed for file %s", Dic_File_Name );
       errmsg[ERRMSGLEN-1] = '\0';
       FetchErrorText(dwErrCode, errmsg, errbuf, errbuflen );
       return(FALSE);
    }
  }

  //MAP THE FILE
  // Create a file mapping object for the file.
  hDicFileMap = CreateFileMapping (hDicFile, NULL, PAGE_READONLY, 0, dwDicFileSize, NULL);
  if (hDicFileMap == INVALID_HANDLE_VALUE)
  {
    DWORD dwErrCode = GetLastError();
    char errmsg[ERRMSGLEN];
    _snprintf(errmsg, ERRMSGLEN, "Error calling CreateFileMapping for file %s", Dic_File_Name );
    errmsg[ERRMSGLEN-1] = '\0';
    FetchErrorText(dwErrCode, errmsg, errbuf, errbuflen );
    return(FALSE);
  }

  //CREATE
  // Map the view
  lpDicMapBase = MapViewOfFile(hDicFileMap,        // handle to mapping object
                              FILE_MAP_READ,       // read permission
                              0,                   // high-order 32 bits of file offset
                              0,                   // low-order 32 bits of file offset
                              dwDicFileSize);      // number of bytes to map
  if (lpDicMapBase == NULL)
  {
    DWORD dwErrCode = GetLastError();
    FetchErrorText(dwErrCode, "Call to 'MapViewOfFile' failed. lpDicMapBase returned is NULL.", errbuf, errbuflen );
    return(FALSE);
  }

  //NOW TRY SOME SANITY CHECKS
  dichead = (struct dichead_layout *) lpDicMapBase;
  if ( !(    dichead->id[1] == 'E'
          && dichead->id[2] == 'D'
          && dichead->id[3] == 'X'
          && dichead->id[4] == 'd'
          && dichead->id[5] == 'i'
          && dichead->id[6] == 'c'
          && dichead->id[7] == 't' ) )
  {
    //NOT EDX DICTIONARY. ERROR IN HEADER.
    _snprintf(errbuf, errbuflen, "File %s is not an EDX dictionary file. Header does not begin with 'EDXdict'", Dic_File_Name );
    errbuf[errbuflen-1] = '\0';
    return(FALSE);
  }
  if (dichead->id[0] == 5)    //Dictionary version 5 contains 'flags'
  {
    Extended_ANSI_Guessing = (dichead->flags & 0x00000001);
  }
  else
  {
    if (dichead->id[0] != 4)    //Dictionary version 4
    {
      //WRONG DICTIONARY VERSION
      _snprintf(errbuf, errbuflen, "EDX dictionary file %s is not version 4 or 5. Version is %d", Dic_File_Name, dichead->id[0] );
      errbuf[errbuflen-1] = '\0';
      return(FALSE);
    }
    Extended_ANSI_Guessing = FALSE;
  }
  return(TRUE);
}

/*****************************************************************************/
BOOL load_aux1_dic(char *Aux1_File_Name, char *errbuf, int errbuflen)
{
  FILE *fpAux1File = NULL;  //User's Aux1 dictionary
  HANDLE hAux1File;         //Handle to user's Aux1 dictionary
  DWORD dwAux1FileSize;     //Length of user's Aux1 dictionary. Used to determine how much memory to allocate.

  //User's personal Aux1 dictionary is optional.
  if (Aux1_File_Name == "") {return(TRUE);}

  //Save Aux1 filename
  strncpy(Aux1File,Aux1_File_Name,FNAMESIZE);
  Aux1File[FNAMESIZE-1] = '\0';

  //OPEN USER'S PERSONAL DICTIONARY (AUX1) and get the size
  hAux1File = CreateFile (Aux1_File_Name,
                          GENERIC_READ,
                          FILE_SHARE_READ,
                          NULL,
                          OPEN_ALWAYS,
                          0,
                          NULL);
  if (hAux1File == INVALID_HANDLE_VALUE)
  {
    DWORD dwErrCode = GetLastError();
    char errmsg[ERRMSGLEN];
    _snprintf(errmsg, ERRMSGLEN, "Error opening %s", Aux1_File_Name );
    errmsg[ERRMSGLEN-1] = '\0';
    FetchErrorText(dwErrCode, errmsg, errbuf, errbuflen );
    return(FALSE);
  }

  //GET SIZE OF AUX1 FILE
  dwAux1FileSize = GetFileSize(hAux1File, NULL);
  if (dwAux1FileSize == 0xFFFFFFFF)
  {
    DWORD dwErrCode = GetLastError();
    if (dwErrCode != NO_ERROR)
    {
       char errmsg[ERRMSGLEN];
       _snprintf(errmsg, ERRMSGLEN, "Call to 'GetFileSize' failed for file %s", Aux1_File_Name );
       errmsg[ERRMSGLEN-1] = '\0';
       FetchErrorText(dwErrCode, errmsg, errbuf, errbuflen );
       return(FALSE);
    }
  }
  CloseHandle(hAux1File);

  fpAux1File = fopen(Aux1_File_Name,"r");
  if (fpAux1File == (FILE *) NULL)
  {
    char errmsg[ERRMSGLEN];
    _snprintf(errmsg, ERRMSGLEN, "Error reopening user's personal dictionary file %s.\n", Aux1_File_Name);
    errmsg[ERRMSGLEN-1] = '\0';
    return(FALSE);
  }

  aux1base = new unsigned char[dwAux1FileSize+2];  //+1 for leading length byte of first word, +1 for trailing NULL byte of last word
  if (aux1base == 0)
  {
    DWORD dwErrCode = GetLastError();
    char errmsg[ERRMSGLEN];
    _snprintf(errmsg, ERRMSGLEN, "Memory allocation failure.");
    errmsg[ERRMSGLEN-1] = '\0';
    FetchErrorText(dwErrCode, errmsg, errbuf, errbuflen );
    return(FALSE);
  }
  aux1ptr = aux1base;  /* Current address into user's AUX1 personal lexical database */

//------------------------------------------------------------------------------
  /* MAIN LOOP. READ FROM USER'S PERSONAL AUX1 DICTIONARY, ADD TO MEMORY DATABASE */
   int i,j,
       ln_len,  /* line length */
       wd_len,  /* word length */
       wdbeg;
   int linenum = 0;  /* line number */

   #define WDBUF_SIZE    80    /* Inword buffer */
   unsigned char  wdbuf[WDBUF_SIZE];
   char signedwdbuf[WDBUF_SIZE];

   while ( fgets(signedwdbuf,WDBUF_SIZE,fpAux1File) != 0)
   {
      ++linenum;                /* line # of file we're reading */
      ln_len = strlen(signedwdbuf);   /* Save length of line */
      if (ln_len == WDBUF_SIZE)
      {
         char errmsg[ERRMSGLEN];
         _snprintf(errmsg, ERRMSGLEN, "Input line too long in user's personal dictionary file.\nLine %d, file %s.\n", linenum, Aux1_File_Name);
         errmsg[ERRMSGLEN-1] = '\0';
         return(FALSE);
      }

      /* Lowercase the string */
      for ( i = 0; i < ln_len; ++i )
         wdbuf[i] = ANSItolower( (unsigned char)signedwdbuf[i] );

      /* skip over leading spaces and tabs until we find beginning of word or end of line */
      for ( wdbeg = 0;
             EDXisspace(wdbuf[wdbeg])
            &&
             wdbeg < ln_len;
           ++wdbeg );

      if (wdbeg < ln_len)   /* Is begining of word (else was a blank line)*/
      {
         /* Get length of word */
         for (  j = wdbeg, wd_len=0 ;
                j < ln_len
             && !EDXisspace(wdbuf[j]);
                ++j, ++wd_len );

         if ( wd_len > 31 )
         {
            wdbuf[wdbeg+wd_len] = 0;                    /* make ASCIZ string */
            char errmsg[ERRMSGLEN];
            _snprintf(errmsg, ERRMSGLEN, "Word too long in user's personal dictionary file.\nMax length is 31 characters.\nLine %d, file %s, word '%s'\n", linenum, Aux1_File_Name, &wdbuf[wdbeg]);
            errmsg[ERRMSGLEN-1] = '\0';
            return(FALSE);
         }

/* Move word to output */
         *aux1ptr++ = (unsigned char) wd_len;         /* Length-byte preceeding each word */
         for (  i = 0, j = wdbeg;
                i < wd_len;
                ++i, ++j )
         {
            *aux1ptr++ = wdbuf[j];
         }
      }/*endif we have a word*/
   }/* END MAIN LOOP */

/* Assume we exit loop because fgets reached End Of File. (No fancy error checking) */
  *aux1ptr++ = '\0';      /* NULL after last word indicates end of lexical word list*/
  fclose(fpAux1File);
  return(TRUE);
}
/******************************************************************************/
// Dic_File_Name is name of main EDX spelling dictionary (the EDX lexical database file)
// Aux1_File_Name is the name of the user's personal auxiliary spelling dictionary (Aux1)
BOOL spell_init(char *Dic_File_Name, char *Aux1_File_Name, char *errbuf, int errbuflen)
{
  if (dic_loaded) { return(TRUE); }

  if ( !load_main_dic(Dic_File_Name, errbuf, errbuflen) ) return(FALSE);

  if ( !load_aux1_dic(Aux1_File_Name, errbuf, errbuflen) ) return(FALSE);

  dic_loaded = TRUE;  //dic_loaded now means both main dictionary and optinal aux1 dictionary
  return(TRUE);
}

/*---------------------------------------------------------------------------
    .SUBTITLE BINSRCH_MAINDIC

 Functional Description:
    The index to the dictionary main lexical database is searched
    to determine the page range within which target_word must lie
    if it exists.

 Calling Sequence:
    binsrch_maindic( &low, &high, &target_word, &errbuf, errbuflen );

 Argument inputs:
    target_word - character array of word to match, blank padded to
                      dichead->indswd (by reference)

 Outputs:
    low - dictionary page number below which word would not reside (by reference)
    high - dictionary page number above which word would not reside (by reference)
    (NOTE: The first dictionary page number is 0.)

---------------------------------------------------------------------------*/
void binsrch_maindic( DWORD *low,
                      DWORD *high,
                      unsigned char *target_word )
{
   unsigned char *dicindptr = (unsigned char *)dichead + dichead->indofst;  /* Starting address of index */
   int cmp;     /* Result of memory compare memcmp */
   DWORD newdpn;  /* new dictionary page number to try */

/* PREPARE FOR BINARY SEARCH */
   *high = dichead->nidxwds - 1;   /* Highest dictionary page number [minus one because we start count at zero](number of index guide words. One guide word for each page.) */
   *low = 0;  /* Start at low dictionary page number = 0 (first page)*/

/* BINARY SEARCH THE INDEX */
   for (;;)
   {
      newdpn = (*low + *high)/2;
      if (newdpn == *low) break;           /* exitloop when guess=lowb */
      cmp = memcmp(target_word, dicindptr + newdpn*dichead->indswd, dichead->indswd);
      if (cmp == 0) break;          /* switch to linear search */
      if (cmp > 0) *low = newdpn;          /* word is in higher half */
      else *high = newdpn;             /* else word is in lower half */
   }/*endloop */

/* NOW DO LINEAR SEARCH UP AND DOWN TO FIND TRUE PAGE BOUNDARIES */
/* FIRST LOOK TOWARD Z'S FOR newdpn > TARGET_INDEX OR END OF DICTIONARY */
/* Set upper bound page #.  NOTE: Search is to INCLUDE this page up to
first length-byte.  Word we are looking for may be at the end of prev
page spilling over into this page.  ALSO NOTE: if word is in very last
page of dictionary past last guide word then we must increment high by
one to include the last page.  */
   *high = dichead->nidxwds -1;   /* number of last page in dictionary [minus one because we start count at zero](number of index guide words) */
   while( (cmp = memcmp(target_word,
                       dicindptr + newdpn*dichead->indswd,
                       dichead->indswd))
          >= 0  &&  newdpn != *high ) ++newdpn;
   *high = newdpn;             /* Set upper bound page # */
   if (cmp >= 0) ++*high;       /* include very last page of dictionary if need be */


/* SEARCH FOR newdpn < TARGET_INDEX OR BEGINNING OF DICTIONARY */
   while( memcmp(target_word,
                 dicindptr + newdpn*dichead->indswd,
                 dichead->indswd)
          <= 0  &&  newdpn != 0 ) --newdpn;
   *low = newdpn;  /* set lower bound page # */
}

/*=============================================================================
    .SUBTITLE DIC_LOOKUP_WORD

 Functional Description:
    Searches the EDX dictionary for a given word

 Calling Sequence:
    status = dic_lookup_word(wdlen, wdbeg, errbuf, errbuflen, Dic_File_Name, Aux1_File_Name)

 Argument inputs:
    wdlen - length of word
    wdbeg - pointer to start of word
    errbuf - buffer to put any error message in to return to caller (let caller display it)
    errbuflen - length of errbuf.
    Dic_File_Name - name of dictionary file to pass to Spell_Init
    Aux1_File_Name - name of user's personal dictionary file to pass to Spell_Init.
                     May be NULL "" if user does not have a personal dictionary file.
                     A user's personal dictionary file is a plain text file with
                     one word per line. This file is checked when spell checking
                     and when spell guessing.

 Outputs:
    status = EDX__WORDFOUND - word was found
           = EDX__WORDNOTFOUND - word was not found
           = EDX__ERROR - an error was encountered. Error text returned in 'errbuf'

 Outline:
    1.  The input word is copied to target_word buffer and lowercased.

    2.  The dictionary common word list is searched for the word.

    3.  The main lexical database is searched for the word.

---------------------------------------------------------------------------*/

int dic_lookup_word(int wdlen, unsigned char *wdbeg, char *errbuf, int errbuflen, char *Dic_File_Name, char *Aux1_File_Name)
{
   DWORD i;
   DWORD low;       /* lower bound page # */
   DWORD high;      /* upper bound page # */
   unsigned char *wdend;     /* word pointer */
   unsigned char *wdptr;     /* word pointer */
   unsigned char *dptr;      /* pointer into dictionary into word */
   unsigned char *lbptr;     /* pointer to length-byte of current word */
   unsigned char *tptr;      /* pointer into target_word */
   unsigned char *endrange;
   DWORD target_word_len;            /* length of target word */
   unsigned char target_word[MAXWORDLEN+1];   /* word spelling checker is currently checking */

   if (!spell_init(Dic_File_Name,Aux1_File_Name,errbuf,errbuflen)) { return(EDX__ERROR); }

   unsigned char *cmnwdsptr = (unsigned char *)dichead + dichead->cwdofst;  /* Starting address of common words */
   unsigned char *diclexdba = (unsigned char *)dichead + dichead->lexofst;  /* Starting address of main lexical database */
   //char *dicindptr = (char *)dichead + dichead->indofst;  /* Starting address of index */
/* NOTE: pages referred to are edx_dictionary pages of size DICPLN */

   /* SETUP_DICWORD */
   /* Move misspelled word to storage place, lowercase, and blank pad
      to INDSWD in length (so we can compare it with guide words) */

   if (wdlen == 0) return(EDX__WORDFOUND);     /* accept zero length word as OK */
   if (wdlen > MAXWORDLEN) return(EDX__WORDNOTFOUND); /* Word too long.  Can't possibly be a word.  User probably doesn't want us to stop on it anyway. */
   wdend = wdbeg + wdlen;               /* wdend -> char after last char of word */
   for ( wdptr = wdbeg, i = 0;
         wdptr < wdend;
         ++wdptr, ++i )
      target_word[i] = ANSItolower(*wdptr);
   target_word_len = wdlen;

   for ( ; i < dichead->indswd; ++i )          /* BLANK PAD TO INDSWD LENGTH */
      target_word[i] = SPACE;

/* SEARCH COMMON WORD LIST FOR MATCH */
   if (target_word_len <= dichead->cwdmln)     /* skip if target_word is too long to be in commonword list */
   {
      endrange = cmnwdsptr + dichead->cwdlen;  /* end of commonwords */
      lbptr = cmnwdsptr;                       /* start at beginning of common words */
      while (lbptr < endrange)                 /* still in range of dictionary we're searching */
      {
         if (*lbptr == 0x00) break;            /* End of Lexical Database */
         if ((DWORD)*lbptr == target_word_len)         /* check if word lengths match first */
         {
            for ( tptr = target_word + target_word_len -1,  /* start tptr at last char of target_word */
                  dptr = lbptr + target_word_len;           /* start dptr at last char of word in dictionary */
                  tptr >= target_word && *tptr == *dptr;    /* while chars match up to beginning of word */
                  --tptr, --dptr);                          /* move back a char */
            if (tptr < target_word) return(EDX__WORDFOUND); /* word found */
         }
         lbptr += *lbptr + 1;                   /* move to next word */
      }
   }

/* SEARCH MAIN DICTIONARY FOR MATCH */
   binsrch_maindic( &low, &high, (unsigned char *)&target_word );

/* Linear search dictionary pages for match to target word.  Compare
   found word with target word starting with last character and moving
   to front of word.  We do this because we already expect the first
   few characters of the word to match if we're looking in the right
   area of the dictionary.
*/
   endrange = diclexdba + (high * dichead->dicpln);

/*//DEBUG
   char *lbptra = diclexdba + (low * dichead->dicpln);
   char *diclexend = diclexdba + dichead->lexlen;
   sprintf(errbuf,"low=%u high=%u dichead=%x diclexdba=%x diclexend=%x lbptra=%x lbptr=%x endrange=%x *lbptra=%c *lbptr=%c",low,high,dichead,diclexdba,diclexend,lbptra,lbptr,endrange,*lbptra,*lbptr);
   return(31);
*/

   for ( lbptr = diclexdba + (low * dichead->dicpln); *lbptr > 31; ++lbptr);  /* find a length-byte */
   while (lbptr < endrange)
   {
      if (*lbptr == 0x00) break;                            /* End of Lexical Database */
      if ((DWORD)*lbptr == target_word_len)                 /* check if word lengths match first */
      {
         for ( tptr = target_word + target_word_len -1,     /* start tptr at last char of target_word */
               dptr = lbptr + target_word_len;              /* start dptr at last char of word in dictionary */
               tptr >= target_word && *tptr == *dptr;       /* while chars match up to beginning of word */
               --tptr, --dptr);                             /* move back a char */
         if (tptr < target_word) return(EDX__WORDFOUND);    /* word found */
      }
      lbptr += *lbptr + 1;                  /* move to next word */
   }

/* SEARCH USER'S PERSONAL AUX1 DICTIONARY FOR MATCH */
   if (aux1base != NULL)  //If there is a user's personal Aux1 dictionary
   {
      lbptr = aux1base;                        /* start at beginning of words */
      while (TRUE)
      {
         if (*lbptr == 0x00) break;            /* End of Lexical Database */
         if ((DWORD)*lbptr == target_word_len)         /* check if word lengths match first */
         {
            for ( tptr = target_word + target_word_len -1,  /* start tptr at last char of target_word */
                  dptr = lbptr + target_word_len;           /* start dptr at last char of word in dictionary */
                  tptr >= target_word && *tptr == *dptr;    /* while chars match up to beginning of word */
                  --tptr, --dptr);                          /* move back a char */
            if (tptr < target_word) return(EDX__WORDFOUND); /* word found */
         }
         lbptr += *lbptr + 1;                   /* move to next word */
      }
   }

/* DROP OUT BOTTOM IF WORD NOT FOUND IN MAIN DICTIONARY */
   return(EDX__WORDNOTFOUND);      /* WORD NOT FOUND ANYWHERE.  SORRY */
}

/*===============================================================================
 * Main entry point. Fills in globals dic_lwa with word, dic_lwl with word length,
 * Resets GMODE, GOF, and GSUBMODE for possible call to edx$spell_guess
 Functional Description:
    Searches the EDX dictionary for a given word

 Calling Sequence:
    status = edx$dic_lookup_word(char *spellword, char *errbuf, int errbuflen, char *Dic_File_Name, char *Aux1_File_Name);

 Argument inputs:
    spellword - word to check spelling of
    errbuf - buffer to put any error message in to return to caller (let caller display it)
    errbuflen - length of errbuf.
    Dic_File_Name - name of EDX dictionary file to pass to Spell_Init
    Aux1_File_Name - name of user's personal dictionary file to pass to Spell_Init.
                     May be NULL "" if user does not have a personal dictionary file.
                     A user's personal dictionary file is a plain text file with
                     one word per line. This file is checked when spell checking
                     and when spell guessing.

 Outputs:
    status = EDX__WORDFOUND - word was found
           = EDX__WORDNOTFOUND - word was not found
           = EDX__ERROR - an error was encountered. Error text returned in 'errbuf'
 *===============================================================================*/
extern "C" _declspec (dllexport) int edx$dic_lookup_word(char *spellword, char *errbuf, int errbuflen, char *Dic_File_Name, char *Aux1_File_Name)
{
   gof = gsubmode = 0;                 /* reset GMODE, GOF, and GSUBMODE, incase we start spell guessing */
   gmode = GUSREV;
   strncpy( (char *)dic_lwa,spellword,MAXWORDLEN);
   dic_lwl = strlen(spellword);
 __try
 {
   return( dic_lookup_word(dic_lwl, dic_lwa, errbuf, errbuflen, Dic_File_Name, Aux1_File_Name) );
 }
 __except(GetExceptionCode()==EXCEPTION_IN_PAGE_ERROR ?
            EXCEPTION_EXECUTE_HANDLER : EXCEPTION_CONTINUE_SEARCH)
 {
   // Failed to read from the view.
   LOAD_EIPE_ERROR_MESSAGE
   return(EDX__ERROR);
 }
}
/*--------------------------------------------------------------------------
    .SUBTITLE SPELL_GUESS

 Functional Description:
    Guesses the spelling of misspelled word stored in DIC_LWA,DIC_LWL.
    Algorythm taken from the very popular Vassar Spelling Checker.
    With credit to Vassar where credit is due.

 Outline:
    1.  spell_gusrev   Reversals   (test for transposed characters)
    2.  spell_gusvol   vowels      (test for wrong vowel used)
    3.  spell_gusmin   minus chars (test for extra character in word)
    4.  spell_guspls   plus chars  (test for character missing from word)
    5.  spell_guscon   consonants  (test for wrong character used)
    6.  give up     (give up)

Updated 11/03/2006
 I defined Extended_ANSI_Guessing. If TRUE, spell guessing will use
 those extended characters with accents in spell guessing.
 Characters such as š œ ž ß à á â ã ä å æ ç è é ê ë ì í î ï ð ñ ò ó ô õ ö ø ù ú û ü ý þ ÿ


---------------------------------------------------------------------------*/
BOOL spell_gusrev(unsigned char *guess_word)
{
   int status;
   unsigned char temp;

   /* Guess reversals.
      Copy word and transpose x with x+1 */
   while(gof < dic_lwl-1)                      /* test for beyond end of word */
   {
      if (dic_lwa[gof] != dic_lwa[gof+1])      /* don't swap if characters are identical */
      {
         memcpy(guess_word,dic_lwa,dic_lwl);   /* copy over word */
         guess_word[dic_lwl] = '\0';
         temp = guess_word[gof];               /* swap chars */
         guess_word[gof] = guess_word[gof+1];
         guess_word[gof+1] = temp;
         status = dic_lookup_word( dic_lwl, guess_word, "", 0, "", "" );   /* see if word exists */
         //status = EDX__WORDFOUND; //for debugging
         if (status == EDX__WORDFOUND)
         {
            ++gof;                             /* move to next character for reentry */
            return(TRUE);                      /* return with guessword containing a correctly spelled word, status */
         }
      }
      ++gof;                        /* move to next character */
   }
   return(FALSE);         /* no more guess words found */
}
/*-------------------------------------------------------------------------------*/
BOOL spell_gusvol(unsigned char *guess_word)
{
   int status;
   unsigned int topcase;

   /* Guess vowel replacements.
      For each {a,e,i,o,u} replace with {a,e,i,o,u}
      GSUBMODE goes from 0-4 as letter replacement goes a,e,i,o,u

      11/03/2006
      Added Extended_ANSI_Guessing. If defined, then we include all those other
      extended vowels with accents, and we do
      For each {a,e,i,o,u} replace with {a,e,i,o,u}
      GSUBMODE goes from 0-28 as letter replacement goes a,e,i,o,u...

   */
   while(gof < dic_lwl)                 /* test for beyond end of word */
   {
      memcpy(guess_word,dic_lwa,dic_lwl);   /* copy over word */
      guess_word[dic_lwl] = '\0';

      if ( ISVOWEL(guess_word[gof]) )
      {
         if (Extended_ANSI_Guessing){
            topcase = 28;
         }else{
            topcase = 4;
         }
         while(gsubmode <= topcase)
         {
            switch (gsubmode)
            {
               case  0: guess_word[gof] = 'a'; break;    /* 1 = replace with an "a" */
               case  1: guess_word[gof] = 'e'; break;    /* 2 = replace with an "e" */
               case  2: guess_word[gof] = 'i'; break;    /* 3 = replace with an "i" */
               case  3: guess_word[gof] = 'o'; break;    /* 4 = replace with an "o" */
               case  4: guess_word[gof] = 'u'; break;    /* 5 = replace with an "u" */
               case  5: guess_word[gof] = A_WITH_GRAVE; break;        // 224
               case  6: guess_word[gof] = A_WITH_ACUTE; break;        // 225
               case  7: guess_word[gof] = A_WITH_CIRCUMFLEX; break;   // 226
               case  8: guess_word[gof] = A_WITH_TILDE; break;        // 227
               case  9: guess_word[gof] = A_WITH_DIAERESIS; break;    // 228
               case 10: guess_word[gof] = A_WITH_RING_ABOVE; break;   // 229
//       || guess_word[gof] == AE; break;                // 230
//       || guess_word[gof] == C_WITH_CEDILLA; break;    // 231
               case 11: guess_word[gof] = E_WITH_GRAVE; break;        // 232
               case 12: guess_word[gof] = E_WITH_ACUTE; break;        // 233
               case 13: guess_word[gof] = E_WITH_CIRCUMFLEX; break;   // 234
               case 14: guess_word[gof] = E_WITH_DIAERESIS; break;    // 235
               case 15: guess_word[gof] = I_WITH_GRAVE; break;        // 236
               case 16: guess_word[gof] = I_WITH_ACUTE; break;        // 237
               case 17: guess_word[gof] = I_WITH_CIRCUMFLEX; break;   // 238
               case 18: guess_word[gof] = I_WITH_DIAERESIS; break;    // 239
//       || guess_word[gof] == ETH; break;               // 240
//       || guess_word[gof] == N_WITH_TILDE; break;      // 241
               case 19: guess_word[gof] = O_WITH_GRAVE; break;        // 242
               case 20: guess_word[gof] = O_WITH_ACUTE; break;        // 243
               case 21: guess_word[gof] = O_WITH_CIRCUMFLEX; break;   // 244
               case 22: guess_word[gof] = O_WITH_TILDE; break;        // 245
               case 23: guess_word[gof] = O_WITH_DIAERESIS; break;    // 246
//#define (this is the division sign)              // 247
               case 24: guess_word[gof] = O_WITH_STROKE; break;       // 248
               case 25: guess_word[gof] = U_WITH_GRAVE; break;        // 249
               case 26: guess_word[gof] = U_WITH_ACUTE; break;        // 250
               case 27: guess_word[gof] = U_WITH_CIRCUMFLEX; break;   // 251
               case 28: guess_word[gof] = U_WITH_DIAERESIS; break;    // 252
//       || guess_word[gof] == Y_WITH_ACUTE      // 253
//       || guess_word[gof] == THORN             // 254
//       || guess_word[gof] == Y_WITH_DIAERESIS  // 255
               default:  return(FALSE);   /* Should never get here. return but don't signal */
            }
            if (guess_word[gof] != dic_lwa[gof])    /* if we didn't replace vowel with same vowel */
            {
               status = dic_lookup_word( dic_lwl, guess_word, "", 0, "", "" );   /* see if word exists */
               //status = EDX__WORDFOUND; //for debugging
               if (status == EDX__WORDFOUND)
               {
                  ++gsubmode;           /* set to guess next vowel for next time */
                  return(TRUE);         /* return with guess_word containing a correctly spelled word, status */
               }/*endif(status);*/
            }/*endif(guess_word[gof]!=dic_lwa[gof]);*/
            ++gsubmode;                 /* move to next vowel */
         }/*endwhile(gsubmode < 5 or 29)*/
         gsubmode=0;                    /* reset gsubmode */
      }/*endif(guessword=aeiou*/
      ++gof;                        /* move to next character */
   }/*endwhile(gof<dic_lwl-1)*/
   return(FALSE);             /* no more guesses */
}
/*-------------------------------------------------------------------------------*/
BOOL spell_gusmin(unsigned char *guess_word)
{
   int status;

   /* Guess minus.  Test for extra character.
      Try eliding one character at a time */
   if (dic_lwl < 2) {return(FALSE);}         /* skip this test if eliding a character would leave us with an empty string */
   while(gof < dic_lwl)                     /* test for beyond end of word */
   {
      if (gof == 0 || dic_lwa[gof] != dic_lwa[gof-1])       /* skip if prev char = current char. The result would be the same */
      {                                                     /*  as last time.  (Also check gof==0 first) */
         memcpy(&guess_word[0],&dic_lwa[0],gof);            /* copy over word */
         memcpy(&guess_word[gof],&dic_lwa[gof+1],dic_lwl-(gof+1));/* shift GOF'th+1 to end of word left one */
         guess_word[dic_lwl-1] = '\0';
         status = dic_lookup_word( dic_lwl-1, guess_word, "", 0, "", "" );   /* see if word exists */
         //status = EDX__WORDFOUND; //for debugging
         if (status == EDX__WORDFOUND)
         {
            ++gof;              /* move to next char for reentry */
            return(TRUE);       /* return with guess_word containing a correctly spelled word, status */
         }/*endif(status);*/
      }/*endif(not double char)*/
      ++gof;                    /* move to next char */
   }/*endwhile(gof<dic_lwl)*/
   return(FALSE);             /* no more guesses */
}

/*-------------------------------------------------------------------------------*/
BOOL spell_guspls(unsigned char *guess_word)
{
   int status;
   unsigned char guess_char;

   /* Guess plus.  Test if a letter is missing from word.  Add one letter anywhere in word.
      GSUBMODE goes from 0-25 as letter replacement goes from a-z
      11/03/2006
      If 'Extended_ANSI_Guessing' is TRUE, then we include all those other
      extended characters with accents, and we do
      GSUBMODE goes from 0-25 as letter replacement goes from a-z
      then
      GSUBMODE jumps to 223 and goes from 223-255, skipping 247 (division sign)
         (see file "EDX_lowercasing_entended_letters.htm")   */
   while(gof <= dic_lwl)                    /* test for beyond end of word */
   {
      memcpy(&guess_word[0],&dic_lwa[0],gof);           /* copy over word */
      memcpy(&guess_word[gof+1],&dic_lwa[gof],dic_lwl-gof); /* shift GOF'th+1 to end of word left one */
      guess_word[dic_lwl+1] = '\0';

      while(gsubmode <= 255)                  /* test for GSUBMODE<=255 (all extended letters of alphabet) */
      {
         if (gsubmode ==  26)
         {
            if (Extended_ANSI_Guessing) {gsubmode = 154;}  /* skip up to extended chars */
            else {break;}                        /* Jump out of while loop. We are done.  */
         }
         if (gsubmode == 155) {++gsubmode;}      /* skip SINGLE RIGHT-POINTING ANGLE QUOTATION MARK */
         if (gsubmode == 157) {++gsubmode;}      /* skip (not used) */
         if (gsubmode == 159) {gsubmode = 223;}  /* jump to LATIN SMALL LETTER SHARP S */
         if (gsubmode == 247) {++gsubmode;}      /* skip DIVISION SIGN */
         if (gsubmode < 26){guess_char = (unsigned char)gsubmode + (unsigned char)'a';}  /* convert GSUBMODE={0-25} to ASCII {A-Z} (which is {65-90} */
         else {guess_char = (unsigned char)gsubmode;}        /* convert GSUBMODE={223-255} to ANSI (see file "EDX_lowercasing_entended_letters.htm") */

         if (gof == 0 || guess_char != dic_lwa[gof-1])      /* if extra char being inserted = char it's infront of */
         {                                                  /*  then don't do it to avoid duplicates */
            guess_word[gof] = guess_char;                   /* insert missing letter */
            status = dic_lookup_word( dic_lwl+1, guess_word, "", 0, "", "" );   /* see if word exists */
            //status = EDX__WORDFOUND; //for debugging
            if (status == EDX__WORDFOUND)
            {
               ++gsubmode;          /* set to try next char on reentry */
               return(TRUE);        /* return with string containing a correctly spelled word, status */
            }/*endif(status);*/
         }/*endif(not double char)*/
         ++gsubmode;                /* try next char */
      }/*endwhile(gsubmode<=255)*/

      gsubmode=0;               /* reset gsubmode */
      ++gof;                    /* move to next char */
   }/*endwhile(gof<dic_lwl)*/
   return(FALSE);             /* no more guesses */
}

/*-------------------------------------------------------------------------------*/
BOOL spell_guscon(unsigned char *guess_word)
{
   int status;
   int isvowel;
   unsigned char guess_char;

   /* Guess consonants.  Test for any one character wrong.
      Replace each character with every other character of the alphabet
      GSUBMODE goes from 0-25 as letter replacement goes from a-z
      If 'Extended_ANSI_Guessing' is TRUE, then we include all those other
      extended characters with accents, and we do
      GSUBMODE goes from 0-25 as letter replacement goes from a-z
      then
      GSUBMODE jumps to 223 and goes from 223-255, skipping 247 (division sign)
         (see file "EDX_lowercasing_entended_letters.htm")
      We've already tried replacing vowel characters with other vowel characters,
      so if we're on a vowel, then skip if our replacement character is also a vowel.
      Also skip if our guess character is the same as the original character.
   */
   while(gof < dic_lwl)                 /* test for beyond end of word */
   {
      if ( ISVOWEL(dic_lwa[gof]) )
         isvowel = TRUE;
      else
         isvowel = FALSE;

      while(gsubmode <= 255)                  /* test for GSUBMODE<=255 (all extended letters of alphabet) */
      {
         if (gsubmode ==  26)
         {
            if (Extended_ANSI_Guessing) {gsubmode = 223;}  /* skip up to extended chars */
            else {break;}                        /* Jump out of while loop. We are done.  */
         }
         if (gsubmode == 247) {gsubmode = 248;}  /* skip division sign */

         if (gsubmode < 26){guess_char = (unsigned char)gsubmode + (unsigned char)'a';}  /* convert GSUBMODE={0-25} to ASCII {A-Z} (which is {65-90} */
         else {guess_char = (unsigned char)gsubmode;}        /* convert GSUBMODE={223-255} to ANSI (see file "EDX_lowercasing_entended_letters.htm") */

         if (   (guess_char != dic_lwa[gof])            /* if overstrike char != original char */
             && ( !ISVOWEL(guess_char) )               /* and char being replaced isn't a vowel */
            )
         {                          /*  or then don't do it to avoid duplicates */
            memcpy(guess_word,dic_lwa,dic_lwl);         /* copy over word */
            guess_word[dic_lwl] = '\0';
            guess_word[gof] = guess_char;               /* overstrike with another letter */
            status = dic_lookup_word( dic_lwl, guess_word, "", 0, "", "" );   /* see if word exists */
            //status = EDX__WORDFOUND; //for debugging
            if (status == EDX__WORDFOUND)
            {
               ++gsubmode;          /* set to try next char on reentry */
               return(TRUE);        /* return with string containing a correctly spelled word, status */
            }/*endif(status);*/
         }/*endif(not double char)*/
         ++gsubmode;                /* try next char */
      }/*endwhile(gsubmode<=255)*/

      gsubmode=0;               /* reset gsubmode */
      ++gof;                    /* move to next char */
   }/*endwhile(gof<dic_lwl)*/
   return(FALSE);             /* no more guesses */
}

/*--------------------------------------------------------------------------
    .SUBTITLE SPELL_GUESS

 Functional Description:
    Guesses the spelling of misspelled word stored in DIC_LWA,DIC_LWL.
    Algorythm taken from the very popular Vassar Spelling Checker.
    With credit to Vassar where credit is due.

 Calling Sequence:
    result = edx$spell_guess(char *guessword, char *errbuf, int errbuflen,);

 Argument inputs:
    char *guessword pointer to ASCIZ string. Must be at least 33 characters long! This is where we put our guessword.
    errbuf - buffer to put any error message in to return to caller (let caller display it)
    errbuflen - length of errbuf.
    DIC_LWA = TARGET_WORD - Address of misspelled word
    DIC_LWL = TARGET_WORD_LEN - Length of misspelled word
    GMODE   - guess mode    (1=reversals,2=vowels,3=minus,4=plus,5=consonants,6=giveup)
    GOF - guess column offset (character # in word working on)
    GSUBMODE- (char) guess submode (letter we're currently replacing with)
     (NOTE: gmode = GUSREV, gof = gsubmode = 0; SET BY DIC_LOOKUP_WORD)

 Outputs:
    retcode=EDX__WORDFOUND, guessword = guessed word. Here's another word to try.
     or
    retcode = EDX__WORDNOTFOUND, no more guesses.

 Outline:
    1.  Reversals   (test for transposed characters)
    2.  vowels      (test for wrong vowel used)
    3.  minus chars (test for extra character in word)
    4.  plus chars  (test for character missing from word)
    5.  consonants  (test for wrong character used)
    6.  give up     (give up)

Updated 11/03/2006
 I defined Extended_ANSI_Guessing. If TRUE, spell guessing will use
 those extended characters with accents in spell guessing.
 Characters such as š œ ž ß à á â ã ä å æ ç è é ê ë ì í î ï ð ñ ò ó ô õ ö ø ù ú û ü ý þ ÿ


---------------------------------------------------------------------------*/

extern "C" _declspec (dllexport) int edx$spell_guess(char *guessword, char *errbuf, int errbuflen)
{
 __try
 {
   switch (gmode)               /* GUESS MODE */
   {
      case GUSREV:              /* 1 = GUESS REVERSALS */
           if (spell_gusrev( (unsigned char *)guessword) ) return(EDX__WORDFOUND);      /* EDX__WORDFOUND if guess word found. outstr set.  gcol, gmode, gsubmode hold our place for reentry */
           ++gmode;             /* go to next guess mode */
           gof = gsubmode = 0;          /* reset GOF and GSUBMODE */
                        /* DROP THROUGH TO NEXT GUESS MODE */
      case GUSVOL:              /* 2 = GUESS VOWELS */
           if (spell_gusvol( (unsigned char *)guessword) ) return(EDX__WORDFOUND);      /* EDX__WORDFOUND if guess word found. outstr set.  gcol, gmode, gsubmode hold our place for reentry */
           ++gmode;             /* go to next guess mode */
           gof = gsubmode = 0;          /* reset GOF and GSUBMODE */
                        /* DROP THROUGH TO NEXT MODE: GUSMIN */
      case GUSMIN:              /* 3 = GUESS MINUS */
           if (spell_gusmin( (unsigned char *)guessword) ) return(EDX__WORDFOUND);      /* EDX__WORDFOUND if guess word found. outstr set.  gcol, gmode, gsubmode hold our place for reentry */
           ++gmode;             /* go to next guess mode */
           gof = gsubmode = 0;          /* reset GOF and GSUBMODE */
                        /* DROP THROUGH TO NEXT MODE: GUSPLS */
      case GUSPLS:              /* 4 = GUESS PLUS */
           if (spell_guspls( (unsigned char *)guessword) ) return(EDX__WORDFOUND);      /* EDX__WORDFOUND if guess word found. outstr set.  gcol, gmode, gsubmode hold our place for reentry */
           ++gmode;             /* go to next guess mode */
           gsubmode = 0;            /* reset GSUBMODE */
           gof = 0;             /* reset GOF */
                        /* DROP THROUGH TO NEXT MODE: GUSCON */
      case GUSCON:              /* 5 = GUESS CONSONANTS */
           if (spell_guscon( (unsigned char *)guessword) ) return(EDX__WORDFOUND);      /* EDX__WORDFOUND if guess word found. outstr set.  gcol, gmode, gsubmode hold our place for reentry */
                        /* DROP THROUGH TO NEXT MODE: GIVEUP */
      case GIVEUP:              /* 6 = GIVE UP */
           guessword[0] = '\0';
           return( EDX__WORDNOTFOUND );        /* no more guesses */
   }
   return( EDX__WORDNOTFOUND );        /* (should never end up here) */
 }
 __except(GetExceptionCode()==EXCEPTION_IN_PAGE_ERROR ?
            EXCEPTION_EXECUTE_HANDLER : EXCEPTION_CONTINUE_SEARCH)
 {
   // Failed to read from the view.
   LOAD_EIPE_ERROR_MESSAGE
   return(EDX__ERROR);
 }
}

/*-----------------------------------------------------------------------------
    .SBTTL  ADD WORD TO USER'S AUX1 DICTIONARY

 Functional Description:
    This routine adds a word to the user's personal aux1 dictionary.

  Calling Sequence:
    result = edx$add_persdic(char *newword, char *errbuf, int errbuflen);

 Argument inputs:
    newword - pointer to ASCIZ string containing new word to add to user's Aux1 personal dictionary
    errbuf - buffer to put any error message in to return to caller (let caller display it)
    errbuflen - length of errbuf.

 Outline:
 1. Open for append, or create, user's personal dictionary file.
    The user's personal dictionary file is a plain text file with one word per line.
 2. delete previously allocated memory that we loaded user's personal dictionary in
 3. Append word to user's personal dictionary file.
 4. Close user's personal dictionary file.
 5. Call load_aux1_dic to reload it, now with new word included.
---------------------------------------------------------------------------*/
extern "C" _declspec (dllexport) int edx$add_persdic(char *newword, char *errbuf, int errbuflen)
{
  // 1. Open for append, or create, user's personal dictionary file.
  //    The user's personal dictionary file is a plain text file with one word per line.
  FILE *fpAux1File = NULL;  //User's Aux1 dictionary

  if (!strlen(Aux1File))
  {
    char errmsg[ERRMSGLEN];
    _snprintf(errmsg, ERRMSGLEN, "Error adding word to user's personal auxiliary dictionary.\nUser's personal auxiliary dictionary filename not set.\n");
    errmsg[ERRMSGLEN-1] = '\0';
    return(EDX__ERROR);
  }

  fpAux1File = fopen(Aux1File,"a");
  if (fpAux1File == (FILE *) NULL)
  {
    char errmsg[ERRMSGLEN];
    _snprintf(errmsg, ERRMSGLEN, "Error opening user's personal dictionary file %s.\n", Aux1File);
    errmsg[ERRMSGLEN-1] = '\0';
    return(EDX__ERROR);
  }

  // 2. delete previously allocated memory that we loaded user's personal dictionary in
  if (aux1base) { delete[] aux1base; }  // User's personal Aux1 dictionary in memory

  // 3. Append word to user's personal dictionary file.
  fprintf(fpAux1File,"%s\n",newword);

  // 4. Close user's personal dictionary file.
  fclose(fpAux1File);

  // 5. Call load_aux1_dic to reload it, now with new word included.
  if ( !load_aux1_dic(Aux1File, errbuf, errbuflen) ) return(EDX__ERROR);

  return(EDX__WORDFOUND);  //signal success
}


/*-----------------------------------------------------------------------------
    .SBTTL  SHOW VERSION NUMBER

 Functional Description:
    This routine returns the version number of this module

 Calling Sequence:
    edx$dll_version(buf,buflen);
---------------------------------------------------------------------------*/
extern "C" _declspec (dllexport) void edx$dll_version(char *buf, int buflen)
{
// User should send us a buffer with buflen at least 550 to hold whole message.
#define EDX$X_VERSION "EDX Spelling Checker file edxspell.dll version 7.2 November 26, 2006."
#define NOTLOADED     "\nEDX dictionary file is not yet loaded."
#define EDXLOADED     "\nEDX dictionary file is loaded."
#define AUX1LOADED    "\nUser's personal auxiliary dictionary file is: "
#define VERSNO4       "\nEDX dictionary file is version 4"
#define VERSNO5       "\nEDX dictionary file is version 5 (Extended ANSI character compatible)"
#define EXANSISET     "\nExtended ANSI characters exist in the dictionary.\nExtended ANSI Guessing is: ON."
#define EXANSICLEAR   "\nThere are no extended ANSI characters in the dictionary.\nExtended ANSI Guessing is: OFF."

    if (buflen < 1) {return;}

    if (!dic_loaded)
    {
      _snprintf(buf, buflen, "%s%s\n", EDX$X_VERSION, NOTLOADED);
    }
    else
    {
      if (dichead->id[0] == 4)
      {
        _snprintf(buf, buflen, "%s%s%s%s\n", EDX$X_VERSION, VERSNO4, AUX1LOADED, Aux1File);
      }
      else
      {
        if (dichead->id[0] == 5)
        {
          if (Extended_ANSI_Guessing)
          {
            _snprintf(buf, buflen, "%s%s%s%s%s\n", EDX$X_VERSION, VERSNO5, EXANSISET, AUX1LOADED, Aux1File);
          }
          else
          {
            _snprintf(buf, buflen, "%s%s%s%s%s\n", EDX$X_VERSION, VERSNO5, EXANSICLEAR, AUX1LOADED, Aux1File);
          }
        }
      }
    }
    buf[buflen-1] = '\0';
}
