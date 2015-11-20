"""Elpy backend using the Rope library.

This backend uses the Rope library:

http://rope.sourceforge.net/

"""

import os
import time
import traceback

import rope.contrib.codeassist
import rope.base.project
import rope.base.libutils
import rope.base.exceptions
import rope.contrib.findit

from elpy import rpc
import elpy.pydocutils

VALIDATE_EVERY_SECONDS = 5
MAXFIXES = 5


class RopeBackend(object):
    """The Rope backend class.

    Implements the RPC calls we can pass on to Rope. Also subclasses
    the native backend to provide methods Rope does not provide, if
    any.

    """
    name = "rope"

    def __init__(self, project_root):
        super(RopeBackend, self).__init__()
        self.last_validation = 0
        if not os.path.exists(project_root):
            project_root = ""
        self.project_root = project_root
        self.completions = {}
        prefs = dict(ignored_resources=['*.pyc', '*~', '.ropeproject',
                                        '.hg', '.svn', '_svn', '.git'],
                     python_files=['*.py'],
                     save_objectdb=False,
                     compress_objectdb=False,
                     automatic_soa=True,
                     soa_followed_calls=0,
                     perform_doa=True,
                     validate_objectdb=True,
                     max_history_items=32,
                     save_history=False,
                     compress_history=False,
                     indent_size=4,
                     extension_modules=[],
                     import_dynload_stdmods=True,
                     ignore_syntax_errors=False,
                     ignore_bad_imports=False)
        self.project = rope.base.project.Project(self.project_root,
                                                 ropefolder=None,
                                                 **prefs)

    def get_resource(self, filename):
        if filename is not None and os.path.exists(filename):
            return rope.base.libutils.path_to_resource(self.project,
                                                       filename,
                                                       'file')
        else:
            return None

    def validate(self):
        """Validate the stored project.

        This should be called before every use of Rope. It will
        revalidate the project, but do some call throttling.

        """
        now = time.time()
        if now > self.last_validation + VALIDATE_EVERY_SECONDS:
            try:
                self.project.validate()
            except rope.base.exceptions.ResourceNotFoundError:
                pass
            self.last_validation = now

    def call_rope(self, rope_function, filename, source, offset,
                  **kwargs):
        self.validate()
        resource = self.get_resource(filename)
        try:
            return rope_function(self.project,
                                 source, offset,
                                 resource,
                                 maxfixes=MAXFIXES,
                                 **kwargs)
        except (rope.base.exceptions.BadIdentifierError,
                rope.base.exceptions.ModuleSyntaxError,
                rope.base.exceptions.ResourceNotFoundError,
                IndentationError,
                LookupError,
                AttributeError):
            return None
        except Exception as e:
            data = {
                "traceback": traceback.format_exc(),
                "rope_debug_info": {
                    "project_root": self.project_root,
                    "filename": filename,
                    "source": source,
                    "function_name": (rope_function.__module__ +
                                      "." +
                                      rope_function.__name__),
                    "function_args": ", ".join([
                        "project", "source", str(offset), "resource",
                        "maxfixes={0}".format(MAXFIXES)
                    ] + [
                        u"{}={}".format(k, v)
                        for (k, v) in kwargs.items()
                    ])
                }
            }
            raise rpc.Fault(
                code=500,
                message=str(e),
                data=data
            )

    def rpc_get_completions(self, filename, source, offset):
        proposals = self.call_rope(
            rope.contrib.codeassist.code_assist,
            filename, source, offset
        )
        if proposals is None:
            return []
        try:
            starting_offset = rope.contrib.codeassist.starting_offset(source,
                                                                      offset)
        except (rope.base.exceptions.BadIdentifierError,
                rope.base.exceptions.ModuleSyntaxError,
                IndentationError,
                LookupError,
                AttributeError):
            return []
        prefixlen = offset - starting_offset
        self.completions = dict((proposal.name, proposal)
                                for proposal in proposals)
        try:
            return [{'name': proposal.name,
                     'suffix': proposal.name[prefixlen:],
                     'annotation': proposal.type,
                     'meta': str(proposal)}
                    for proposal in proposals]
        except rope.base.exceptions.ModuleSyntaxError:
            # Bug#406
            return []

    def rpc_get_completion_docstring(self, completion):
        proposal = self.completions.get(completion)
        if proposal is None:
            return None
        else:
            return proposal.get_doc()

    def rpc_get_completion_location(self, completion):
        proposal = self.completions.get(completion)
        if proposal is None:
            return None
        else:
            if not proposal.pyname:
                return None
            module, lineno = proposal.pyname.get_definition_location()
            if module is None:
                return None
            resource = module.get_module().get_resource()
            return (resource.real_path, lineno)

    def rpc_get_definition(self, filename, source, offset):
        location = self.call_rope(
            rope.contrib.findit.find_definition,
            filename, source, offset
        )
        if location is None:
            return None
        else:
            return (location.resource.real_path, location.offset)

    def rpc_get_calltip(self, filename, source, offset):
        offset = find_called_name_offset(source, offset)
        if 0 < offset < len(source) and source[offset] == ')':
            offset -= 1

        calltip = self.call_rope(
            rope.contrib.codeassist.get_calltip,
            filename, source, offset,
            remove_self=True
        )
        if calltip is None:
            return None

        calltip = calltip.replace(".__init__(", "(")
        calltip = calltip.replace("(self)", "()")
        calltip = calltip.replace("(self, ", "(")
        # "elpy.tests.support.source_and_offset(source)"
        # =>
        # "support.source_and_offset(source)"
        try:
            openpos = calltip.index("(")
            period2 = calltip.rindex(".", 0, openpos)
            period1 = calltip.rindex(".", 0, period2)
            calltip = calltip[period1 + 1:]
        except ValueError:
            pass
        return calltip

    def rpc_get_docstring(self, filename, source, offset):
        return self.call_rope(
            rope.contrib.codeassist.get_doc,
            filename, source, offset
        )


def find_called_name_offset(source, orig_offset):
    """Return the offset of a calling function.

    This only approximates movement.

    """
    offset = min(orig_offset, len(source) - 1)
    paren_count = 0
    while True:
        if offset <= 1:
            return orig_offset
        elif source[offset] == '(':
            if paren_count == 0:
                return offset - 1
            else:
                paren_count -= 1
        elif source[offset] == ')':
            paren_count += 1
        offset -= 1


##################################################################
# A recurring problem in Rope for Elpy is that it searches the whole
# project root for Python files. If the user edits a file in their
# home directory, this can easily read a whole lot of files, making
# Rope practically useless. We change the file finding algorithm here
# to only recurse into directories with an __init__.py file in them.
def find_source_folders(self, folder):
    for resource in folder.get_folders():
        if self._is_package(resource):
            return [folder]
    result = []
    for resource in folder.get_files():
        if resource.name.endswith('.py'):
            result.append(folder)
            break
    for resource in folder.get_folders():
        if self._is_package(resource):
            result.append(resource)
    return result

import rope.base.pycore
rope.base.pycore.PyCore._find_source_folders = find_source_folders


def get_files(self):
    if self.files is None:
        self.files = get_python_project_files(self.project)
    return self.files

rope.base.project._FileListCacher.get_files = get_files


def get_python_project_files(project):
    for dirname, subdirs, files in os.walk(project.root.real_path):
        for filename in files:
            yield rope.base.libutils.path_to_resource(
                project, os.path.join(dirname, filename), 'file')
            subdirs[:] = [subdir for subdir in subdirs
                          if os.path.exists(os.path.join(dirname, subdir,
                                                         "__init__.py"))]


##################################################################
# Monkey patching a method in rope because it doesn't complete import
# statements.

orig_code_completions = (rope.contrib.codeassist.
                         _PythonCodeAssist._code_completions)


def code_completions(self):
    proposals = get_import_completions(self)
    if proposals:
        return proposals
    else:
        return orig_code_completions(self)


def get_import_completions(self):
    if not self.word_finder.is_import_statement(self.offset):
        return []
    modulename = self.word_finder.get_primary_at(self.offset)
    # Rope can handle modules in packages
    if "." in modulename:
        return []
    return dict((name, FakeProposal(name))
                for name in elpy.pydocutils.get_modules()
                if name.startswith(modulename))


class FakeProposal(object):
    def __init__(self, name):
        self.name = name
        self.type = "mock"

    def get_doc(self):
        return None

rope.contrib.codeassist._PythonCodeAssist._code_completions = code_completions
