class ValidationError(Exception):

    def __init__(self, message, errors):
        super().__init__(message)
        self.message = message
        self.errors = errors

    def __errPrint__(self, foo, space=' '):
        '''
            Function to petty print the error from cerberus.
        '''
        error = ''
        for key in foo.keys():
            error += space + str(key) + ":"
            if isinstance(foo[key], list):
                for e in foo[key]:
                    error += f'\n{space} - {e}'
            elif isinstance(foo[key][0], dict):
                error += "\n" + self.__errPrint__(foo[key][0], space + space)
            elif isinstance(foo[key][0], list):
                for e in foo[key][0]:
                    error += f'\n{space} - {e}'
            else:
                error += str(foo[key][0])
            error += "\n"
        return error.rstrip()

    def __str__(self):
        return self.message + "\n" + self.__errPrint__(self.errors)
