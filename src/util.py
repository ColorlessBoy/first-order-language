from functools import wraps

def type_check(validType):
    def inner_type_check(func):
        @wraps(func)
        def head_check(*args):
            if args is not None:
                new_args = []
                for arg in args:
                    if isinstance(arg, validType):
                        new_args.append(arg)
                    else:
                        try:
                            arg = validType(arg)
                            new_args.append(arg)
                        except:
                            raise TypeError(f"Arguments are required to be {validType}.")
            return func(*new_args)
        return head_check
    return inner_type_check
    