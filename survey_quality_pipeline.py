import os
from io import StringIO
import pandas as pd
import numpy as np
import re
import math
import unicodedata
from itertools import combinations as it_combinations
from collections import Counter
from scipy.stats import percentileofscore
from scipy.stats import zscore
from thefuzz import fuzz
from datasketch import MinHash
import xml.etree.ElementTree as ET
from functools import partial
from datetime import datetime, timedelta
import sys
import requests

SURVEY_ID = '2412130'
CROSSTAB_ID = 'gpmvpyyy5jdz3e2g'
LAYOUT_ID = '85875'
MAIN_FOLDER = r'Z:\Projects\Uitgekookt\24102024UIT005 Reality Analytics 2025\Data\0. Weekly cleaning'

# OFFSET specifies the number of weeks to adjust within the weekly cleaning cycle.
# For example:
# - Set OFFSET = 0 to focus on last week's cycle.
# - Set OFFSET = -1 to adjust to the cycle from two weeks ago.
# - Set OFFSET = 1 to focus on the current week's cycle.
# - Set OFFSET = 2 to prepare for next week's cycle, and so on.

OFFSET = 0

def get_iso_week(offset=OFFSET):
    """
    Calculates the ISO week based on the current date with an optional offset.

    :param offset: Number of weeks to offset from the current week (e.g., -1 for last week).
    :return: ISO week formatted as YYYYWW.
    """
    date = datetime.now() + timedelta(weeks=offset)
    year, week, _ = date.isocalendar()
    return f"{year}{week:02d}"

xml_data = '''
<root>
   <row label="b1" value="1">Uitgekookt</row>
    <row label="b2" value="2">Apetito</row>
    <row label="b3" value="3">Maaltijdservice.nl</row>
    <row label="b4" value="4">HelloFresh</row>
    <row label="b5" value="5">MaaltijdThuis</row>
    <row label="b6" value="6">Vers aan tafel</row>
    <row label="b7" value="7">Ohmyguts</row>
    <row label="b8" value="8">Thuysvers</row>
    <row label="b9" value="9">Marleen</row>
    <row label="b10" value="10">Crisp</row>
    <row label="b11" value="11">Factor</row>
 </root>'''

# Remove colon from attribute names for easier parsing
xml_data = re.sub(r'cs:', '', xml_data)

# Parse XML data
root = ET.fromstring(xml_data)

# Initialize an empty dictionary to store brand data
brands_dict = {}

def clean_string(s):
    """
    Cleans and normalizes brand strings by removing non-alphabetical characters,
    common words, and converting to lowercase.

    Args:
        s (str): The brand string to clean.

    Returns:
        str: A cleaned and normalized version of the input string.
    """
    s = unicodedata.normalize('NFKD', s).encode('ASCII', 'ignore').decode('utf-8')
    s = re.sub(r'[^a-zA-Z0-9 ]', '', s).lower()  # Keep alphanumeric and spaces
    if len(re.sub(r'[^a-zA-Z]', '', s)) <= 3:  # Remove spaces if too short
        s = s.replace(" ", "")
    return s

# Process each row in the XML
for row in root.findall("row"):
    brand_name = row.text.lower()
    label_value = int(row.attrib["label"][1:])

    # Store data in brands_dict
    brands_dict[brand_name] = {
        "Brand": brand_name,
        "Value": label_value
    }

# Create a tokenized dictionary for additional mapping
excluded_tokens = {}
tokenized_brands_dict = {}
for brand, value in brands_dict.items():
    tokens = brand.split()
    for token in tokens:
        cleaned_token = clean_string(token)
        if cleaned_token in excluded_tokens:
            continue
        if cleaned_token not in tokenized_brands_dict:
            tokenized_brands_dict[cleaned_token] = value

# Normalize the main dictionary for case-insensitive lookups
brands_dict = {key.lower(): value for key, value in brands_dict.items()}

print(brands_dict)
print(tokenized_brands_dict)

def adjust_threshold_for_special_cases(cleaned_respondent_input, best_match):
    """
    Adjusts the threshold for brand matching based on specific rules and special cases.

    Parameters:
    cleaned_respondent_input (str): The cleaned respondent-provided brand input.
    best_match (str): The best match for the cleaned respondent input from a predefined brand list.

    Returns:
    int or None: The adjusted threshold value. Returns `None` if the input is invalid.

    Rules:
    - If the similarity ratio is below 60, a threshold of 100 is returned.
    - If `cleaned_respondent_input` is 'nan' or `None`, `None` is returned.
    - Special cases are checked first and take precedence.
    - Thresholds are adjusted based on the length of the input and best match:
        - Short names (<= 5 characters): Threshold = 76.
        - Short names with long respondent answers: Threshold = 81.
        - Long names (>= 8 characters): Threshold = 76.
    - A default threshold of 75 is returned if no other rules apply.
    """
    if fuzz.ratio(cleaned_respondent_input, best_match) < 60:
        return 100

    if cleaned_respondent_input == 'nan' or cleaned_respondent_input is None:
        return None

    special_cases = {
        ("", ""): 90,
    }

    # Check for special cases first
    if (cleaned_respondent_input, best_match) in special_cases:
        return special_cases.get((cleaned_respondent_input, best_match))

    # Threshold for specific brands
    brand_specific = {}

    # Higher threshold for short brand names (<= 4 characters)
    if len(cleaned_respondent_input) <= 5 and len(best_match) <= 5:
        return 76

    # Higher threshold for short brand names with long respondent answers
    if len(cleaned_respondent_input) > 4 and len(best_match) <= 4:
        return 81

    # Higher threshold for long brand names (>= 8 characters)
    if len(cleaned_respondent_input) >= 8 or len(best_match) >= 8:
        return 76

    if cleaned_respondent_input in brand_specific or best_match in brand_specific:
        brand = cleaned_respondent_input if cleaned_respondent_input in brand_specific else best_match
        return brand_specific[brand]

    return 75

'''
In the blacklist, you can add words that should not be going through the recoding process at all.
'''
blacklist = []

def recode_brand(respondent_input: str) -> int:
    """
    Recodes a respondent's brand input by matching it to a predefined list of valid brands.

    Steps:
    1. Exact match with brands_dict.
    2. Tokenized exact match with tokenized_brands_dict.
    3. Fuzzy token match with tokenized_brands_dict (score > 85).
    4. Fuzzy full-input match with brands_dict (score > threshold).
    5. Return 99 if no match is found.

    Parameters:
    respondent_input (str): The raw input provided by the respondent.

    Returns:
    int: A numeric code representing the matched brand, or 99 if no match is found.
    """
    if respondent_input is None:
        return 99
    cleaned_input = clean_string(respondent_input.strip().lower())

    if not cleaned_input or cleaned_input in ['none', '', 'nan'] or pd.isna(cleaned_input):
        return 99

    print(f"Respondent Input: {cleaned_input}")

    # Step 1: Exact match in brands_dict
    if cleaned_input in brands_dict:
        print(f"EXACT MATCH - Found for '{cleaned_input}'. Returning value: {brands_dict[cleaned_input]['Value']}.")
        return brands_dict[cleaned_input]['Value']

    # Step 2: Tokenized Exact Match
    tokens = [token for token in cleaned_input.split() if token not in blacklist]
    for token in tokens:
        if token in tokenized_brands_dict:
            print(f"EXACT TOKEN MATCH - Found for token '{token}'. Returning value: {tokenized_brands_dict[token]['Value']}")
            return tokenized_brands_dict[token]['Value']

    # Step 3: Fuzzy Token Match
    best_fuzzy_token = None
    best_fuzzy_score = 0
    for token in tokens:
        for tokenized_brand in tokenized_brands_dict.keys():
            score = fuzz.ratio(token, tokenized_brand)
            if score > best_fuzzy_score:
                best_fuzzy_token = tokenized_brand
                best_fuzzy_score = score

    if best_fuzzy_token and best_fuzzy_score >= 85:
        print(f"FUZZY TOKEN MATCH - Found for token: '{best_fuzzy_token}' (Score: {best_fuzzy_score}). Returning value: {tokenized_brands_dict[best_fuzzy_token]['Value']}")
        return tokenized_brands_dict[best_fuzzy_token]['Value']

    # Step 4: Fuzzy Full Input Match
    best_match, highest_score = None, 0
    for brand in brands_dict.keys():
        score = fuzz.ratio(cleaned_input, brand)
        if score > highest_score:
            best_match, highest_score = brand, score

    current_threshold = adjust_threshold_for_special_cases(respondent_input, best_match) or 76

    if best_match and highest_score >= current_threshold:
        print(f"FUZZY FULL BRAND MATCH FOUND: Respondent Input: '{cleaned_input}' matches with '{best_match}' (Score: {highest_score}, "
              f"exceeding threshold of {current_threshold}). Returning value: brands_dict[best_match]['Value']")
        return brands_dict[best_match]['Value']

    # Step 5: Default return if no match
    print("No match found. Returning default value: 99")
    return 99

def recode_brand_conditionally(row, base_col_name, rec_col_name):
    """
    Recodes a brand based on the respondent's language and input, ensuring compatibility with supported languages.

    For languages not supported (e.g., Arabic, Korean, Simplified Chinese, and Thai), the function skips recoding
    and returns the existing value in the `rec_col_name` column. For supported languages, the recoding is performed
    using the `recode_brand` function.

    Parameters:
    row (pd.Series): A row of the DataFrame being processed.
    base_col_name (str): The column name containing the respondent's raw brand input.
    rec_col_name (str): The column name where the recoded brand value will be stored.

    Returns:
    int: The recoded brand value or the existing value if the language is not supported.
    """
    if row['decLang'] not in ['arabic_saudiarabia', 'korean', 'simplifiedchinese', 'thai']:
        return recode_brand(row[base_col_name])
    else:
        return row[rec_col_name]

def split_brands(row, prefix):
    """
    Splits multiple brands mentioned in a respondent's answer into separate columns.

    If a respondent lists multiple brands in a single answer (e.g., 'brand x, brand y, brand z'),
    this function splits them into separate columns (up to 10). Any leftover brands beyond 10
    are ignored. If answers are split, subsequent columns are cleared to avoid overlapping data.

    Parameters:
    row (pd.Series): A single row of the DataFrame being processed.
    prefix (str): The prefix of the column names to process (e.g., 'QBRAW' or 'QADAW').

    Returns:
    pd.Series: The modified row with brands split into separate columns.
    """
    all_brands = []

    # Extract and split brands for each column matching the prefix
    for i in range(1, 11):
        column_name = f'{prefix}01r{i}'
        if column_name in row and pd.notna(row[column_name]):
            # Split by commas or other delimiters
            brands_current = re.split(r',\s*|\s*,', str(row[column_name]))
            all_brands.extend(brands_current)

    # Assign the split brands back into the row (up to 10 columns)
    for i, brand in enumerate(all_brands[:10], start=1):
        column_name = f'{prefix}01r{i}'
        row[column_name] = brand

    # Clear remaining columns (if fewer than 10 brands found)
    for i in range(len(all_brands) + 1, 11):
        column_name = f'{prefix}01r{i}'
        row[column_name] = None

    return row

def shannon_entropy(text):
    """
    Calculates Shannon entropy for a given string.

    :param text: The input string (str).
    :return: The Shannon entropy of the string (float).
    """
    if not text:
        return 0.0

    frequency_dict = Counter(text)
    text_length = len(text)
    probabilities = (count / text_length for count in frequency_dict.values())

    return -sum(p * math.log2(p) for p in probabilities if p > 0)

def dynamic_entropy_threshold(text_length):
    """
    Determines a dynamic entropy threshold based on the length of the input text.

    :param text_length: Length of the input text (int).
    :return: The entropy threshold (float).
    """
    thresholds = {3: 0.5, 5: 1.0, 7: 1.5}
    return thresholds.get(next((k for k in thresholds if text_length <= k), None), 2.0)

def is_keysmash(text, repeat_threshold=4, min_alpha_ratio=0.8):
    """
    Determines if a given text is a keysmash based on low entropy, repeated characters,
    or low ratio of alphabetic characters.

    :param text: The input string (str).
    :param repeat_threshold: Number of repeated characters to consider as a keysmash (int).
    :param min_alpha_ratio: Minimum ratio of alphabetic characters to total length (float).
    :return: True if the text is a keysmash, False otherwise.
    """
    if not text or len(text.strip()) == 0:
        return False

    # Calculate the ratio of alphabetic characters in the text
    num_alpha = sum(1 for char in text if char.isalpha())
    alpha_ratio = num_alpha / len(text)

    # If the text doesn't meet the minimum alphabetical ratio, it's considered a keysmash
    if alpha_ratio < min_alpha_ratio:
        return True

    # Extract only alphabetic characters
    text_alpha_only = ''.join(char for char in text if char.isalpha())
    if not text_alpha_only:
        return False

    # Calculate entropy and repeated character patterns
    entropy = shannon_entropy(text_alpha_only)
    entropy_threshold = dynamic_entropy_threshold(len(text_alpha_only))
    pattern = r'(.)\1{' + f'{repeat_threshold - 1}' + ',}'

    # A keysmash is detected if entropy is low or repeated character patterns are present
    return entropy < entropy_threshold or re.search(pattern, text_alpha_only) is not None

def check_bad_open_answers(df, columns_to_check):
    """
    Evaluates the quality of open-ended answers in a DataFrame based on several metrics.

    :param df: The input DataFrame containing responses (pd.DataFrame).
    :param columns_to_check: List of columns to evaluate (list of str).
    :return: The updated DataFrame with quality metrics and scores (pd.DataFrame).
    """
    valid_exceptions = []
    valid_exceptions.extend(tokenized_brands_dict.keys())

    # Initialize metrics in the DataFrame
    metrics = ['non_alpha_count', 'keysmash_count', 'short_answer_count', 'high_consonant_count', 'high_vowel_count']
    for metric in metrics:
        df[metric] = 0

    df['non_blank_count'] = 0
    df['bad_open_answer_score'] = 0.0

    vowels = set("aeiouAEIOUäöüÄÖÜ")

    for respondent in df.index:
        row = df.loc[respondent]

        for col in columns_to_check:
            answer = df.loc[respondent, col]

            # Skip processing for valid exceptions or null answers
            if pd.isnull(answer):
                continue

            # Count non-blank answers
            df.loc[respondent, 'non_blank_count'] += 1
            answer = str(answer)

            if str(answer.lower()) in valid_exceptions:
                continue

            if not answer[0].isalpha():
                df.at[respondent, 'non_alpha_count'] += 1

            if is_keysmash(answer, repeat_threshold=4):
                df.at[respondent, 'keysmash_count'] += 1

            if len(answer) <= 2:
                df.at[respondent, 'short_answer_count'] += 1

            num_vowels = sum(1 for char in answer if char in vowels)
            num_alphas = sum(1 for char in answer if char.isalpha())

            if num_alphas > 0:
                percent_consonants = ((num_alphas - num_vowels) / num_alphas) * 100
                if percent_consonants > 85:
                    df.at[respondent, 'high_consonant_count'] += 1

                percent_vowels = (num_vowels / num_alphas) * 100
                if percent_vowels > 85:
                    df.at[respondent, 'high_vowel_count'] += 1

        # Calculate cumulative bad open answer score
        filled_fields = df.at[respondent, 'non_blank_count']
        if filled_fields > 0:
            df.at[respondent, 'bad_open_answer_score'] = sum(df.at[respondent, metric] for metric in metrics) / filled_fields

    return df

def flag_speeders(df):
    """
    Flags respondents as speeders based on outlier detection using IQR applied to log-transformed response times.

    :param df: A DataFrame containing the 'qtime' column.
    :return: The updated DataFrame with a new column 'is_speeder' indicating flagged speeders (1 for speeder, 0 otherwise).
    """
    # Initialize the 'is_speeder' column
    df['is_speeder'] = 0

    # Log-transform qtime to stabilize variance and handle skewness
    df['log_qtime'] = np.log(df['qtime'])

    # Calculate the IQR for log-transformed qtime
    Q1_log = df['log_qtime'].quantile(0.25)
    Q3_log = df['log_qtime'].quantile(0.75)
    IQR_log = Q3_log - Q1_log

    # Determine the lower bound using IQR scaling factor
    lower_bound_log = Q1_log - 0.7 * IQR_log
    lower_bound = np.exp(lower_bound_log)  # Convert back to original scale

    # Flag speeders as those below the lower bound
    df['is_speeder'] = (df['qtime'] < lower_bound).astype(int)

    # Drop the temporary 'log_qtime' column
    df.drop(columns=['log_qtime'], inplace=True)

    return df

def check_straightlining(df):
    """
    Detects straightlining behavior in survey responses by calculating the percentage of the mode frequency
    for each respondent across groups of related survey questions. Updates the DataFrame with scores and flags.

    Parameters:
    df (pd.DataFrame): A DataFrame where rows represent respondents and columns represent survey question responses.

    Returns:
    None: The function modifies the DataFrame in-place by adding:
          - 'straightlining_scores': A score based on the extent of straightlining behavior.
          - 'straightlining_groupnumber': A comma-separated list of groups where straightlining was detected.
          - Additional binary columns for each group indicating straightlining detection.
    """

    groups = {
        **{f"Advertisement {x}": [f"QADEVAL_ad{x}s{y}" for y in range(1, 17)] for x in range(1, 11)},
    }


    # Initialize scoring columns
    df['straightlining_scores'] = 0.0
    df['straightlining_groupnumber'] = ""

    for respondent in df.index:
        total_score = 0.0
        straightlining_groups = []

        for group_name, questions in groups.items():
            # Only use columns that exist in the data
            valid_questions = [q for q in questions if q in df.columns]
            if not valid_questions:
                continue

            subset = df.loc[respondent, valid_questions].dropna()
            if subset.empty:
                continue

            # Check if straightlining occurred
            mode_freq = subset.value_counts().max()
            mode_percent = (mode_freq / len(subset)) * 100

            if mode_percent >= 90:
                total_score += len(subset) ** 2
                df.loc[respondent, f'straightlining_{group_name}'] = 1
                straightlining_groups.append(group_name)
            else:
                df.loc[respondent, f'straightlining_{group_name}'] = 0

        df.loc[respondent, 'straightlining_scores'] = total_score
        if straightlining_groups:
            df.loc[respondent, 'straightlining_groupnumber'] = ','.join(straightlining_groups)

def flag_identical_responses(df, columns_to_check, fuzz_threshold=85, threshold_percentage=0.9, blacklist=[]):
    """
    Flags records with identical or highly similar open-ended responses in a given set of columns.

    :param df: A DataFrame containing the survey responses.
    :param columns_to_check: A list of column names to check for identical or similar responses.
    :param fuzz_threshold: The fuzzy matching threshold for similarity (default: 85).
    :param threshold_percentage: The percentage threshold for identical/fuzzy matches to flag (default: 0.9).
    :param blacklist: A list of answers to exclude from comparison.
    :return: The DataFrame with an additional column 'identical_answers' indicating flagged records.
    """
    # Initialize the 'identical_answers' column
    df['identical_answers'] = 0

    for index, row in df.iterrows():
        # Extract and clean non-null answers from the specified columns
        non_null_answers = row[columns_to_check].dropna().astype(str).str.strip()

        if len(non_null_answers) < 2:
            continue  # Skip if fewer than 2 non-null answers are present

        # Check for exact matches
        exact_counts = non_null_answers.value_counts(normalize=True)
        if (exact_counts >= threshold_percentage).any():
            df.loc[index, 'identical_answers'] += 1
            continue  # Skip fuzzy match checks if exact matches already meet the threshold

        # Check for fuzzy matches
        unique_answers = non_null_answers.unique()
        fuzzy_count = 0
        total_pairs = len(unique_answers) * (len(unique_answers) - 1) // 2  # Total unique answer pairs

        for i, ans1 in enumerate(unique_answers[:-1]):
            for ans2 in unique_answers[i + 1:]:
                if ans1.lower() in blacklist or ans2.lower() in blacklist:
                    continue
                if fuzz.ratio(ans1, ans2) >= fuzz_threshold:
                    fuzzy_count += 1

        # Flag if the ratio of fuzzy matches exceeds the threshold percentage
        if total_pairs > 0 and (fuzzy_count / total_pairs) >= threshold_percentage:
            df.loc[index, 'identical_answers'] += 1

    return df

def minhash_similarity(df, columns_to_check, similarity_threshold=0.85, lower_threshold=0.8):
    """
    Checks for similarity across records in a dataset using MinHash and Jaccard similarity.

    :param df: A DataFrame containing the survey data.
    :param columns_to_check: A list of column names to check for similarity.
    :param similarity_threshold: Jaccard similarity threshold for flagging similarity (default: 0.85).
    :param lower_threshold: Lower threshold for larger answer sets (default: 0.8).
    :return: The DataFrame with an additional 'similar_record' column indicating similar records.
    """
    # Initialize 'similar_record' column
    df['similar_record'] = 0

    # Create MinHash objects for each record
    minhashes = {}
    for index, row in df.iterrows():
        # Drop NaN, convert to string, and filter blanks
        data = row[columns_to_check].dropna().astype(str).str.strip()
        data = [d for d in data if d]

        if data:  # Only process non-empty data
            m = MinHash()
            for d in data:
                m.update(d.encode('utf8'))
            minhashes[index] = (m, set(data))

    # Initialize a set to track similar records
    similar_records_set = set()

    # Compare pairs of records using MinHash and Jaccard similarity
    for idx1, idx2 in it_combinations(minhashes.keys(), 2):
        m1, answer_set1 = minhashes[idx1]
        m2, answer_set2 = minhashes[idx2]

        # Compute Jaccard similarity
        sim = m1.jaccard(m2)

        # Adjust threshold based on set size
        threshold = lower_threshold if len(answer_set1) >= 5 or len(answer_set2) >= 5 else similarity_threshold

        # Check for similarity based on common elements or Jaccard similarity
        common_elements = answer_set1.intersection(answer_set2)
        if len(common_elements) >= 8 or sim > threshold:
            similar_records_set.update([idx1, idx2])

    # Update 'similar_record' column for similar records
    df.loc[list(similar_records_set), 'similar_record'] = 1

    return df

def weighted_sum_row_by_row(df, variable_weights, columns_to_normalize, debug_rows=200):
    """
    Calculates a weighted sum for each row using Min-Max scaling for specified columns.
    """
    # Initialize min/max values for normalization
    min_vals = df[columns_to_normalize].min()
    max_vals = df[columns_to_normalize].max()

    # Handle cases where max_vals equals min_vals (avoid division by zero)
    range_vals = (max_vals - min_vals).replace(0, 1)

    # Normalize columns with Min-Max scaling
    normalized = (df[columns_to_normalize] - min_vals) / range_vals

    # Apply weights and calculate the weighted sum
    weights = pd.Series(variable_weights).reindex(columns_to_normalize).fillna(0)

    # Calculate the score as a weighted sum of normalized values
    weighted_scores = normalized.mul(weights).sum(axis=1) / weights.sum()

    # Add weighted scores as the final score
    df['final_score'] = weighted_scores

    return df

def process_quality_scores(df, columns_to_normalize, variable_weights):
    """
    Processes the quality scores for a DataFrame.
    """
    # Calculate weighted scores and final scores for the entire DataFrame
    df = weighted_sum_row_by_row(df, variable_weights, columns_to_normalize)

    # Compute the 90th percentile from the raw weighted scores
    top_10_percentile_score_raw = df['final_score'].quantile(0.9)

    # Add removal suggestion: flag top 10% of scores based on raw weighted scores
    df['removal_suggestion'] = (df['final_score'] > top_10_percentile_score_raw).astype(int)

    return df

# Define the columns to normalize and the weights
columns_to_normalize = [
    'straightlining_scores',
    'bad_open_answer_score',
    'is_speeder',
    'identical_answers',
    'similar_record',
]

variable_weights = {
    'straightlining_scores': 0.3,
    'bad_open_answer_score': 0.3,
    'is_speeder': 0.15,
    'identical_answers': 0.15,
    'similar_record': 0.1,
}

def export_weekly_data(headers, last_week, offset=OFFSET-1):
    """
    Fetches survey data for the specified week offset, saves it as a tab-delimited text file,
    and returns the file path.

    :param headers: Authentication headers for the API request.
    :param offset: Week offset for determining the segment (default: last week, offset=-1).
    :return: Path to the saved tab-delimited text file or None if an error occurs.
    """
    try:
        # Determine the segment based on the offset
        last_week = get_iso_week(offset)
        segment = last_week[-2:]  # Extract the last two digits (week number)

        # Construct the API URL
        url = f"https://dvj.decipherinc.com/api/v1/surveys/selfserve/2144/{SURVEY_ID}/data?format=tab&layout={LAYOUT_ID}&cond=xt:{CROSSTAB_ID}:{segment}"
        print(f"Fetching data for segment: {segment} (URL: {url})")

        # Fetch data from the API
        response = requests.get(url, headers=headers)
        if response.status_code != 200:
            print(f"API request failed with status code: {response.status_code}")
            return None

        # Ensure response encoding is UTF-8
        response.encoding = 'utf-8'

        # Process the tab-delimited data
        df = pd.read_csv(StringIO(response.text), delimiter='\t')
        print("Data successfully fetched and parsed.")

        # Define directory and file paths
        dir_path = os.path.join(MAIN_FOLDER, last_week)
        os.makedirs(dir_path, exist_ok=True)
        file_path = os.path.join(dir_path, f"{last_week}_data_APIexported.txt")

        # Save as a tab-delimited text file
        df.to_csv(file_path, index=False, sep='\t', encoding='utf-8')
        print(f"File successfully saved as tab-delimited text to: {file_path}")

        return file_path

    except Exception as e:
        print(f"Error occurred while trying to export data: {e}")
        return None

def main():
    """
    Main function to orchestrate data processing.
    """
    columns_to_check = ['QFLEX07', 'QADAWb', 'QSE01','QFLEX02','RedenOverweging','RedenNietOverwegen','QADAW ','QADAWRec' ]
    brand_input = [f"QBRAW01r{x}" for x in range(1, 11)]
    brand_asso = [f"QBASSO01_b{x}r{y}" for x in (1,2,3,4,8,11) for y in range(1, 11)]
    ad_awareness = [f"QADAW01r{x}" for x in range(1, 11)]
    open_ends = brand_input + brand_asso+ad_awareness
    columns_to_check.extend(open_ends)

    print(f"Columns to Check: {columns_to_check}")

    headers = {'x-apikey': "ffcgk30kta73f1fs2dufrz634u4k7djxj9v3vwv071yrnkzptwregpaqask5zrcy"}

    last_week = get_iso_week(offset=OFFSET-1)
    segment = last_week[-2:]

    week_folder = os.path.join(MAIN_FOLDER, last_week)

    if not os.path.exists(week_folder):
        os.makedirs(week_folder)

    log_file_path = os.path.join(week_folder, f'{last_week}_datacleaning_log.txt')

    # Redirect stdout to a log file for the entire function
    original_stdout = sys.stdout
    log_file = open(log_file_path, 'w', encoding='utf-8')  # Open log file outside the try block to keep it open longer
    sys.stdout = log_file

    try:
        # Fetch weekly data
        file_path = export_weekly_data(headers, last_week)
        # file_path = os.path.join(week_folder, f"{last_week}data_APIexported.txt")
        if not file_path:
            print("Failed to fetch data.")
            return

        # Load data into a DataFrame
        df = pd.read_csv(file_path, delimiter='\t', encoding='utf-8')
        print("Data loaded into DataFrame.")
        print(df.head())

        # Flagging and checking
        flag_speeders(df)
        check_straightlining(df)
        check_bad_open_answers(df, columns_to_check)
        flag_identical_responses(df, columns_to_check)
        minhash_similarity(df, columns_to_check)

        # Apply the processing function to the entire DataFrame
        df = process_quality_scores(df, columns_to_normalize, variable_weights)

        for prefix in ['QBRAW', 'QADAW']:
            # Splitting brands
            df = df.apply(split_brands, args=(prefix,), axis=1)

            # Recoding brands
            for i in range(1, 11):
                base_col_name = f"{prefix}01r{i}"
                rec_col_name = f"{prefix}01RECr{i}"
                # Apply the recoding function to the specific column
                df[rec_col_name] = df.apply(lambda row: recode_brand_conditionally(row, base_col_name, rec_col_name), axis=1)

    except Exception as e:
        # Log the exception to the same log file
        print(f"An error occurred: {e}")
        raise

    finally:
        # Restore stdout and close the log file
        sys.stdout = original_stdout
        log_file.close()

    print(f"Correcting column order and saving file")

    # Step 1: Define the core columns
    core_cols = [
        'uuid',
        'is_speeder',
        'straightlining_scores',
        'bad_open_answer_score',
        'identical_answers', 'similar_record',
        'final_score', 'removal_suggestion', 'CL_BadRespondentYN'
    ]

    # Step 2: Ensure separate processing for QBRAW and QADAW
    def get_interleaved_columns(prefix_answer, prefix_rec, count, valid_cols):
        """
        Constructs an interleaved list of answer and rec columns for the given prefixes and count,
        including only the columns present in valid_cols.

        Args:
            prefix_answer (str): Prefix for the answer columns.
            prefix_rec (str): Prefix for the rec columns.
            count (int): Number of columns to generate for each prefix.
            valid_cols (set): Set of existing DataFrame columns.

        Returns:
            list: An interleaved list of columns that exist in valid_cols.
        """
        answer_cols = [f'{prefix_answer}{i}' for i in range(1, count + 1)]
        rec_cols = [f'{prefix_rec}{i}' for i in range(1, count + 1)]
        interleaved = [item for pair in zip(answer_cols, rec_cols) for item in pair]
        return [col for col in interleaved if col in valid_cols]

    valid_cols = set(df.columns)  # Convert DataFrame columns to a set for performance
    braw_cols = get_interleaved_columns('QBRAW01r', 'QBRAW01RECr', 10, valid_cols)
    adaw_cols = get_interleaved_columns('QADAW01r', 'QADAW01RECr', 10, valid_cols)

    # Debugging Output: Check if columns are properly separated
    print("BRAW Cols:", braw_cols)
    print("ADAW Cols:", adaw_cols)

    # Step 3: Deduplicate columns_to_check to avoid re-adding columns
    columns_to_check = [col for col in columns_to_check if
                        col in df.columns and col not in core_cols + braw_cols + adaw_cols]

    # Step 4: Finalize the column order
    cols = core_cols + braw_cols + adaw_cols + columns_to_check

    # Debugging Output: Verify final column order
    print("Final Columns in DataFrame:", cols)

    # Step 5: Reorder the DataFrame
    df = df[cols]

    # Step 6: Save the cleaned file
    df.to_excel(os.path.join(week_folder, f'{last_week}_cleandata.xlsx'), index=False)

if __name__ == "__main__":
    main()