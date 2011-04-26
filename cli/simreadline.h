/*
mgsim: Microgrid Simulator
Copyright (C) 2006,2007,2008,2009,2010,2011  The Microgrid Project.

This library is free software; you can redistribute it and/or
modify it under the terms of the GNU Library General Public
License as published by the Free Software Foundation; either
version 2 of the License, or (at your option) any later version.

This library is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
Library General Public License for more details.

You should have received a copy of the GNU Library General Public
License along with this library; if not, write to the Free Software
Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301, USA
*/
#ifndef SIMREADLINE_H
#define SIMREADLINE_H

#include "sys_config.h"

#include <cstdio>

#ifdef HAVE_LIBREADLINE
# if defined(HAVE_READLINE_READLINE_H)
#  include <readline/readline.h>
# elif defined(HAVE_READLINE_H)
#  include <readline.h>
# else /* !defined(HAVE_READLINE_H) */
extern "C" char *readline ();
# endif /* !defined(HAVE_READLINE_H) */

extern "C" {
  extern char* cmdline;
  extern int (*rl_event_hook)(void);
}

# ifdef HAVE_READLINE_HISTORY
#  if defined(HAVE_READLINE_HISTORY_H)
#   include <readline/history.h>
#  elif defined(HAVE_HISTORY_H)
#   include <history.h>
#  else /* !defined(HAVE_HISTORY_H) */
extern "C" {
  extern void add_history (const char*);
  extern int write_history (const char*);
  extern int read_history (const char*);
}
#  endif /* defined(HAVE_READLINE_HISTORY_H) */
# else
/* no history */
# endif /* HAVE_READLINE_HISTORY */


#else /* !defined(HAVE_LIBREADLINE) */
/* no readline */
#endif /* HAVE_LIBREADLINE */


#include "sim/display.h"
#include <string>
#include <vector>

class CommandLineReader {
    std::string   m_histfilename;
    static Simulator::Display* m_display;

    static int ReadLineHook(void);
public:
    CommandLineReader(Simulator::Display& d);
    ~CommandLineReader();

    char* GetCommandLine(const std::string& prompt);
    void CheckPointHistory();

};

std::vector<std::string> Tokenize(const std::string& str, const std::string& sep);

#endif