import pandas as pd
import sys 

pd.set_option('display.max_columns',None)
pd.set_option('display.max_rows',None)
pd.set_option("display.width",220)

def gray(s): return f"\033[90m{s}\033[0m"
def red(s): return f"\033[91m{s}\033[0m"
def green(s): return f"\033[92m{s}\033[0m"


def format_value(val_gen, val_ref):
    #print(val_gen,val_ref)
    if pd.isna(val_gen):
        return f"{red('/NDF/')} -> {green(str(val_ref))}"
    elif str(val_gen) == str(val_ref):
        return gray(str(val_gen))
    else :
        return f"{red(str(val_gen))} -> {green(str(val_ref))}"
    
def color_diff(df_gen, df_ref):
    df_gen ,df_ref = df_gen.align(df_ref, join="outer",axis=0)
    df_gen ,df_ref = df_gen.align(df_ref, join="outer",axis=1)


    result= pd.DataFrame("",index=df_ref.index,columns=df_ref.columns)

    for col in df_ref.columns:
        result[col]=[
            format_value(df_gen.at[i,col],df_ref.at[i,col])
            for i in df_ref.index
        ]
    return result


if __name__ == "__main__":
    if len(sys.argv) != 3:
        print("usage : diff.py <generated_output> <reference_output>")
        sys.exit(1)
    
    gen_path = sys.argv[1]
    ref_path = sys.argv[2]

    df_gen= pd.read_csv(gen_path,engine="python")
    df_ref= pd.read_csv(ref_path,engine="python")
    #print(df_gen.head())
    


    
    result_df = color_diff(df_gen,df_ref)
    print (result_df)
