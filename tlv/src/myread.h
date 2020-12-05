/* This file should be included by input.lex. */

/* This code is a mess becuase it tries to accomodate both
   to lex and flex. Currently, this file works better with flex.

   The purpose of this file is to allow interactive parsing.
   So we use yyparse to parse the input stream. This introduces
   two issues. First, reading the input using the normal input
   routine is ugly from the user's point of view, since the user
   cannot use arrows to return to previous commands or to move
   inside the line, as one could do from a terminal input.
   To solve this issue we use gnu readline. Much of the code
   in this file is about using gnu readline instead of the default
   method of reading files.

   The second issue is to deal with recursive loads.
   Actually, this is not an issue of interactivity.
   The problem with recursive loads is that each time we
   are loading from a different file, and when we finish
   one file we have to continue reading from where we left
   off in the original file. For this puprose this file
   implements a stack of file handlers and additional data. */

char *prompt = "\n>> ";
char *curr_prompt;
char *empty_prompt = "   ";

/* if READLINE */
#ifdef READLINE
#include <stdio.h>
#include <readline/readline.h>

  /* if SYSTEM!=cyg */
#if SYSTEM!=cyg
#include <readline/history.h>
#endif
  /* End SYSTEM!=cyg */

#endif

#include <sys/types.h>
#include <stdlib.h>
#include "mystring.h"
#include "script.h"
#include "util_err.h"

/* If do_prompt == 1 then we are reading from the terminal.
   do_prompt == 2, raw mode. */
extern char do_prompt;

extern char *input_file;

/* if LEX == flex */
#if LEX == flex
int yylineno;
#else
extern int yylineno;
#endif
/* END  LEX == flex */

int mytemp;
char *temp;

/* Define a stack of input streams */
struct input_stream {
  int lineno;
  char *fname;
  FILE *in;
   /* if LEX == flex */
#if LEX != flex
  char bufstart[YYLMAX];
  char *yysptr;
#endif
   /* END LEX == flex */
};
struct input_stream stream_stack[20];

int ss_top = 0;

void set_prompt()
{
#ifdef READLINE
  curr_prompt = prompt;
#else
  fprintf(tlvstdout, prompt);
#endif
}

void push_stream(void)
{
  stream_stack[ss_top].fname = input_file;
  stream_stack[ss_top].lineno = yylineno;
  stream_stack[ss_top].in = yyin;

#if LEX != flex
  stream_stack[ss_top].yysptr = yysptr;
#endif
  ss_top++;
}

void pop_stream(void)
{
  ss_top--;
  input_file = stream_stack[ss_top].fname;
  yylineno = stream_stack[ss_top].lineno;
  yyin = stream_stack[ss_top].in;
}

/* Allow recursive load by using a stack of streams. */

/*void load_file(node_ptr file_name) */
void load_file(char* file_name)
{
  /* char *file_name = fname->left.strtype->text */
  FILE *in;

  /* Load file ( thus doing the tlv "load" command ) */
  if (! (in = open_file(file_name, 0)) )
    fprintf(tlvstderr, "\nThe file %s has not been found...\n",
            file_name);
  else {
    /* Save current stream in stack. */
    push_stream();

    input_file = file_name;
    yylineno = 1;
    yyin = in;
#if LEX != flex
    yysptr = stream_stack[ss_top].bufstart;
#endif
    do_prompt = 0;
    silent = 1;
  }
}

void init_input(void)
{
#if LEX != flex
  extern char *yysptr;
  yysptr = stream_stack[0].bufstart;
#endif
}

/* ZZZ if LEX == flex */
#if LEX == flex

/* Return number of characters actually read. */
int my_yyinput(char *buf, int maxsize) 
{
  extern int yylineno;

  switch (do_prompt) {
    case 0: {
      char *result = fgets(buf,maxsize,yyin); 
      yylineno++;

      /* EOF has been encountered and no characters have been read */
      if (result == NULL) {
        if (ss_top > 0) {
          fclose(yyin);

          pop_stream();
          do_prompt = (yyin == stdin);

          if (do_prompt)
            set_prompt();
          silent = ! do_prompt;
          return my_yyinput(buf,maxsize);
        }
        else
          return 0; /* EOF */
      }
      else {
        int templen = strlen(buf);

        /* If we are at end of file with no newline, then add
           artificial newline to make sure that the token at the
           end of this file will be separated from the token in
           another file which we might be in the process of loading. */
        if ( feof(yyin) && buf[templen-1] != '\n' ) {
          buf[templen] = '\n';
          templen++;
        }
        return templen;
      }
      break;
    }

  case 1: {
    /* Do prompt. So use readline. */
    yylineno++;

#ifdef READLINE
    temp = readline(curr_prompt);

    curr_prompt = empty_prompt;

    if (!temp) return 0 ;   /* Check for end of file. */

    /* If there is anything on the line, remember it and copy to buffer. */
    if (*temp) {
      int templen = strlen(temp);

      /* Find last char in string, check if CTRL-D, and copy to buffer. */
      for(mytemp = 0; buf[mytemp] = temp[mytemp]; mytemp++) 
        if (temp[mytemp] == '\004')  /* 004 = ctrl-d. */
          exit(1);

      add_history (temp);
      free(temp);
      return templen;
    }
    else {
      /* Return empty line. */
      free(temp);
      buf[0] = '\n';
      buf[1] = 0;
      return 1;
    }
#else
    {
      char *result = fgets(buf,maxsize,yyin); 

      /* EOF has been encountered and no characters have been read */
      if (result == NULL)
        return 0; /* EOF */
      else
        return strlen(buf);
    }

#endif
    break;
  }
  case 2: {
    /* Simple use. Used when reading order file. */
    char *result = fgets(buf,maxsize,yyin);
    int templen = strlen(buf);

    if (result == NULL)
      return 0;

    yylineno++;

    /* If we are at end of file with no newline, then add 
       artificial newline to make sure that the token at the 
       end of this file will be separated from the token in 
       another file which we might be in the process of loading. */
    if (feof(yyin) && buf[templen-1] != '\n') {
      buf[templen] = '\n';
      templen++;
    }
    return templen;
  }
  }
}

#undef YY_INPUT
#define YY_INPUT(buffer,result,maxsize) (result = my_yyinput(buffer,maxsize))

#else
/* ELSE ZZZ if LEX == flex */

/* Returns the next character from the input stream.
   If we are not reading characters from the user, then 
   we use normal getc() to obtain characters from the current
   input file. We manage a stack of input files to accomodate
   for recusive Load commands which call other files.
   If we are reading characters from the user then we use
   gnu readline(). This reads an entire line at once. We simualate
   reading a character at a time by "unputting" the rest of the 
   characters in the line. The "input()" macro will then read
   the unput buffer. */
int get_next_c(void)
{
  if (!do_prompt) {
    int c = getc(yyin);

    if (c == EOF && ss_top > 0) {
      fclose(yyin);

      ss_top--;
      input_file = stream_stack[ss_top].fname;
      yylineno = stream_stack[ss_top].lineno;
      yyin = stream_stack[ss_top].in;
      yysptr = stream_stack[ss_top].yysptr;
      do_prompt = (yyin == stdin);

      if (do_prompt)
        set_prompt();

      silent = ! do_prompt;
      return get_next_c();
    }
    return c;
  }

  /* In this case we *are* printing a prompt. This means that
     we are reading text from the user and thus should try to 
     use readline. */

  temp = readline (curr_prompt);
  curr_prompt = empty_prompt;

  if (!temp) return EOF;   /* Check for end of file. */

  /* If there is anything on the line, remember it and put in buffer. */
  if (*temp) {
    char return_char;
    extern int yylineno;

    yylineno++;
    yyunput('\n');

    /* Find last char in string. */
    for(mytemp = 0;temp[mytemp];mytemp++)
      if (temp[mytemp] == '\004')  /* 004 = ctrl-d. */
        exit(1);

    /* unput characters of string. */
    for (mytemp--;mytemp;mytemp--) yyunput(temp[mytemp]);

    return_char = temp[0];

    add_history(temp);

    free(temp);
    return return_char;
  }
  else {
    free(temp);
    return '\n';
  }
}

#undef input
# define input() (((yytchar= yysptr>stream_stack[ss_top].bufstart ? U(*--yysptr) : get_next_c())\
                        ==10?(yylineno++,yytchar):yytchar)==EOF?0:yytchar)

#undef unput
# define unput(c) {yytchar= (c);if(yytchar=='\n')yylineno--;*yysptr++=yytchar;}

#endif
   /* END ZZZ if LEX == flex  */
/*#endif */


/*void init_prompt()
{
#ifndef READLINE
  printf(prompt);
#endif
}*/
