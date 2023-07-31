import json
from fastapi import FastAPI, HTTPException
from fastapi.staticfiles import StaticFiles
from fastapi.responses import HTMLResponse
from pydantic import BaseModel
from typing import List

app = FastAPI()

# Load existing data from the JSON file
def load_data():
    try:
        with open("comments.json", "r") as file:
            return json.load(file)
    except FileNotFoundError:
        return []

# Save data to the JSON file
def save_data(data):
    with open("comments.json", "w") as file:
        json.dump(data, file, indent=2)

# In-memory data storage (replace with JSON file in production)
comments_data = load_data()

class Comment(BaseModel):
    name: str
    comment: str

app.mount("/static", StaticFiles(directory="static"), name="static")

@app.get("/", response_class=HTMLResponse)
async def read_root():
    return """
    <!DOCTYPE html>
    <html lang="en">
    <head>
      <meta charset="UTF-8">
      <meta name="viewport" content="width=device-width, initial-scale=1.0">
      <title>Comments</title>
      <link rel="stylesheet" href="/static/styles.css">
    </head>
      <div class="container">
    <div class="header">
      <img src="static/coffee.png" alt="Coffee" class="coffee-image">
      <h1>Comments</h1>
    </div>
    <form id="commentForm">
      <label for="name">Name:</label>
      <input type="text" id="name" required>
      <label for="comment">Comment:</label>
      <textarea id="comment" required></textarea>
      <button type="submit">Submit</button>
    </form>
    <div id="commentsSection">
      <!-- Comments will be displayed here -->
    </div>
    <div id="giftSection">
      <!-- Gift will be displayed here -->
    </div>
  </div>
      <script src="/static/script.js"></script>
    </body>
    </html>
    """

@app.post('/comments/', response_model=Comment)
def add_comment(comment: Comment):
    comments_data.append(comment.dict())
    save_data(comments_data)
    return comment

@app.get('/comments/', response_model=List[Comment])
def get_comments():
    return comments_data

@app.delete('/comments/{comment_id}', response_model=Comment)
def delete_comment(comment_id: int):
    if comment_id >= len(comments_data) or comment_id < 0:
        raise HTTPException(status_code=404, detail='Comment not found')
    deleted_comment = comments_data.pop(comment_id)
    save_data(comments_data)
    return deleted_comment
