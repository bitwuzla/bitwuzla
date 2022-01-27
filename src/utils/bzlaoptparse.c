/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */

#include "utils/bzlaoptparse.h"

#include "utils/bzlautil.h"

/*------------------------------------------------------------------------*/

void
bzla_optparse_parse(BzlaMemMgr *mm,
                    int32_t argc,
                    char **argv,
                    BzlaParsedOptPtrStack *opts,
                    BzlaParsedInputPtrStack *infiles,
                    BzlaOpt *bzla_opts,
                    bool (*has_str_arg)(const char *, BzlaOpt *))
{
  assert(mm);
  assert(argc);
  assert(argv);
  assert(opts);
  assert(infiles);
  assert(BZLA_COUNT_STACK(*opts) == 0);
  assert(BZLA_COUNT_STACK(*infiles) == 0);

  int32_t i, j, len;
  BzlaParsedOpt *o;
  BzlaParsedInput *in;
  char *arg, *tmp;

  for (i = 1; i < argc; i++)
  {
    arg = argv[i];
    len = strlen(argv[i]);

    if (arg[0] != '-')
    {
      BZLA_CNEW(mm, in);
      in->mm   = mm;
      in->name = arg;
      BZLA_PUSH_STACK(*infiles, in);
    }
    else
    {
      BZLA_CNEW(mm, o);
      o->mm = mm;

      /* save original option string (without arguments)
       * for error messages */
      BZLA_INIT_STACK(mm, o->orig);
      for (j = 0; j < len && arg[j] != '='; j++)
        BZLA_PUSH_STACK(o->orig, arg[j]);
      BZLA_PUSH_STACK(o->orig, '\0');

      /* extract option name */
      BZLA_INIT_STACK(mm, o->name);
      o->isshrt = arg[1] != '-';
      j         = o->isshrt ? 1 : 2;
      o->isdisable =
          len > 3 && arg[j] == 'n' && arg[j + 1] == 'o' && arg[j + 2] == '-';
      for (j = o->isdisable ? j + 3 : j; j < len && arg[j] != '='; j++)
        BZLA_PUSH_STACK(o->name, arg[j]);
      BZLA_PUSH_STACK(o->name, '\0');

      /* extract option argument (if any) */
      if (arg[j] == '=')
      {
        o->readval = BZLA_ARG_READ_NONE_VIA_EQ;
        o->valstr  = arg + j + 1;
        if (o->valstr[0] != 0)
        {
          o->readval = BZLA_ARG_READ_STR_VIA_EQ;
          o->val     = (uint32_t) strtol(o->valstr, &tmp, 10);
          if (tmp[0] == 0) o->readval = BZLA_ARG_READ_INT_VIA_EQ;
        }
      }
      else
      {
        if (i + 1 < argc && argv[i + 1][0] != '-')
        {
          o->readval = BZLA_ARG_READ_STR;
          o->valstr  = argv[i + 1];
          o->val     = (uint32_t) strtol(o->valstr, &tmp, 10);
          if (tmp[0] == 0)
          {
            o->readval = BZLA_ARG_READ_INT;
            i += 1;
          }
          else if (has_str_arg && has_str_arg(o->name.start, bzla_opts))
          {
            i += 1;
          }
          else
          {
            o->readval = BZLA_ARG_READ_NONE;
            o->valstr  = 0;
          }
        }
      }
      BZLA_PUSH_STACK(*opts, o);
    }
  }
}
