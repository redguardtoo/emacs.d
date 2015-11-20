"""Elpy backend using the Jedi library.

This backend uses the Jedi library:

https://github.com/davidhalter/jedi

"""

import sys
import traceback

import jedi

from elpy import rpc


class JediBackend(object):
    """The Jedi backend class.

    Implements the RPC calls we can pass on to Jedi.

    Documentation: http://jedi.jedidjah.ch/en/latest/docs/plugin-api.html

    """
    name = "jedi"

    def __init__(self, project_root):
        self.project_root = project_root
        self.completions = {}
        sys.path.append(project_root)

    def rpc_get_completions(self, filename, source, offset):
        line, column = pos_to_linecol(source, offset)
        proposals = run_with_debug(jedi, 'completions',
                                   source=source, line=line, column=column,
                                   path=filename, encoding='utf-8')
        if proposals is None:
            return []
        self.completions = dict((proposal.name, proposal)
                                for proposal in proposals)
        return [{'name': proposal.name,
                 'suffix': proposal.complete,
                 'annotation': proposal.type,
                 'meta': proposal.description}
                for proposal in proposals]

    def rpc_get_completion_docstring(self, completion):
        proposal = self.completions.get(completion)
        if proposal is None:
            return None
        else:
            return proposal.docstring(fast=False)

    def rpc_get_completion_location(self, completion):
        proposal = self.completions.get(completion)
        if proposal is None:
            return None
        else:
            return (proposal.module_path, proposal.line)

    def rpc_get_docstring(self, filename, source, offset):
        line, column = pos_to_linecol(source, offset)
        try:
            locations = run_with_debug(jedi, 'goto_definitions',
                                       source=source, line=line, column=column,
                                       path=filename, encoding='utf-8',
                                       re_raise=jedi.NotFoundError)
        except jedi.NotFoundError:
            return None
        if locations:
            return locations[-1].docstring()
        else:
            return None

    def rpc_get_definition(self, filename, source, offset):
        line, column = pos_to_linecol(source, offset)
        try:
            locations = run_with_debug(jedi, 'goto_definitions',
                                       source=source, line=line, column=column,
                                       path=filename, encoding='utf-8',
                                       re_raise=jedi.NotFoundError)
        except jedi.NotFoundError:
            return None
        # goto_definitions() can return silly stuff like __builtin__
        # for int variables, so we fall back on goto() in those
        # cases. See issue #76.
        if (
                locations and
                locations[0].module_path is None
        ):
            locations = run_with_debug(jedi, 'goto_assignments',
                                       source=source, line=line,
                                       column=column,
                                       path=filename, encoding='utf-8')
        if not locations:
            return None
        else:
            loc = locations[-1]
            try:
                if loc.module_path:
                    if loc.module_path == filename:
                        offset = linecol_to_pos(source,
                                                loc.line,
                                                loc.column)
                    else:
                        with open(loc.module_path) as f:
                            offset = linecol_to_pos(f.read(),
                                                    loc.line,
                                                    loc.column)
            except IOError:
                return None
            return (loc.module_path, offset)

    def rpc_get_calltip(self, filename, source, offset):
        line, column = pos_to_linecol(source, offset)
        calls = run_with_debug(jedi, 'call_signatures',
                               source=source, line=line, column=column,
                               path=filename, encoding='utf-8')
        if calls:
            call = calls[0]
        else:
            call = None
        if not call:
            return None
        return {"name": call.name,
                "index": call.index,
                "params": [param.description for param in call.params]}

    def rpc_get_usages(self, filename, source, offset):
        """Return the uses of the symbol at offset.

        Returns a list of occurrences of the symbol, as dicts with the
        fields name, filename, and offset.

        """
        line, column = pos_to_linecol(source, offset)
        try:
            uses = run_with_debug(jedi, 'usages',
                                  source=source, line=line, column=column,
                                  path=filename, encoding='utf-8',
                                  re_raise=(jedi.NotFoundError,))
        except jedi.NotFoundError:
            return []

        if uses is None:
            return None
        result = []
        for use in uses:
            if use.module_path == filename:
                offset = linecol_to_pos(source, use.line, use.column)
            elif use.module_path is not None:
                with open(use.module_path) as f:
                    text = f.read()
                offset = linecol_to_pos(text, use.line, use.column)

            result.append({"name": use.name,
                           "filename": use.module_path,
                           "offset": offset})

        return result


# From the Jedi documentation:
#
#   line is the current line you want to perform actions on (starting
#   with line #1 as the first line). column represents the current
#   column/indent of the cursor (starting with zero). source_path
#   should be the path of your file in the file system.

def pos_to_linecol(text, pos):
    """Return a tuple of line and column for offset pos in text.

    Lines are one-based, columns zero-based.

    This is how Jedi wants it. Don't ask me why.

    """
    line_start = text.rfind("\n", 0, pos) + 1
    line = text.count("\n", 0, line_start) + 1
    col = pos - line_start
    return line, col


def linecol_to_pos(text, line, col):
    """Return the offset of this line and column in text.

    Lines are one-based, columns zero-based.

    This is how Jedi wants it. Don't ask me why.

    """
    nth_newline_offset = 0
    for i in range(line - 1):
        new_offset = text.find("\n", nth_newline_offset)
        if new_offset < 0:
            raise ValueError("Text does not have {0} lines."
                             .format(line))
        nth_newline_offset = new_offset + 1
    offset = nth_newline_offset + col
    if offset > len(text):
        raise ValueError("Line {0} column {1} is not within the text"
                         .format(line, col))
    return offset


def run_with_debug(jedi, name, *args, **kwargs):
    re_raise = kwargs.pop('re_raise', ())
    # Remove form feed characters, they confuse Jedi (jedi#424)
    if 'source' in kwargs:
        kwargs['source'] = kwargs['source'].replace("\f", " ")
    try:
        script = jedi.Script(*args, **kwargs)
        return getattr(script, name)()
    except Exception as e:
        if isinstance(e, re_raise):
            raise
        # Bug jedi#417
        if isinstance(e, TypeError) and str(e) == 'no dicts allowed':
            return None
        # Bug jedi#427
        if isinstance(e, UnicodeDecodeError):
            return None
        # Bug jedi#429
        if isinstance(e, IndexError):
            return None
        # Bug jedi#431
        if isinstance(e, AttributeError) and str(e).endswith("'end_pos'"):
            return None
        # Bug in Python 2.6, see #275
        if isinstance(e, OSError) and e.errno == 13:
            return None
        # Bug jedi#466
        if (
                isinstance(e, SyntaxError) and
                "EOL while scanning string literal" in str(e)
        ):
            return None
        # Bug jedi#482
        if isinstance(e, UnicodeEncodeError):
            return None
        # Bug jedi#485
        if (
                isinstance(e, ValueError) and
                "invalid \\x escape" in str(e)
        ):
            return None
        # Bug jedi#485 in Python 3
        if (
                isinstance(e, SyntaxError) and
                "truncated \\xXX escape" in str(e)
        ):
            return None
        # Bug jedi#465
        if (
                isinstance(e, SyntaxError) and
                "encoding declaration in Unicode string" in str(e)
        ):
            return None
        # Bug #337 / jedi#471
        if (
                isinstance(e, ImportError) and
                "No module named" in str(e)
        ):
            return None
        # Bug #365 / jedi#486 - fixed in Jedi 0.8.2
        if (
                isinstance(e, UnboundLocalError) and
                "local variable 'path' referenced before assignment" in str(e)
        ):
            return None
        # Bug #366 / jedi#491
        if (
                isinstance(e, ValueError) and
                "__loader__ is None" in str(e)
        ):
            return None
        # Bug #353
        if (
                isinstance(e, OSError) and
                "No such file or directory" in str(e)
        ):
            return None

        from jedi import debug

        debug_info = []

        def _debug(level, str_out):
            if level == debug.NOTICE:
                prefix = "[N]"
            elif level == debug.WARNING:
                prefix = "[W]"
            else:
                prefix = "[?]"
            debug_info.append(u"{0} {1}".format(prefix, str_out))

        jedi.set_debug_function(_debug, speed=False)
        try:
            script = jedi.Script(*args, **kwargs)
            return getattr(script, name)()
        except Exception as e:
            source = kwargs.get('source')
            sc_args = []
            sc_args.extend(repr(arg) for arg in args)
            sc_args.extend("{0}={1}".format(k, "source" if k == "source"
                                            else repr(v))
                           for (k, v) in kwargs.items())

            data = {
                "traceback": traceback.format_exc(),
                "jedi_debug_info": {'script_args': ", ".join(sc_args),
                                    'source': source,
                                    'method': name,
                                    'debug_info': debug_info}
            }
            raise rpc.Fault(message=str(e),
                            code=500,
                            data=data)
        finally:
            jedi.set_debug_function(None)
