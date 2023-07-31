const commentsSection = document.getElementById('commentsSection');
const giftSection = document.getElementById('giftSection');

// Fetch comments from the server and display them on the page
async function fetchComments() {
  try {
    const response = await fetch('/comments/');
    const data = await response.json();

    commentsSection.innerHTML = '';
    data.forEach((comment, index) => {
      const commentElement = document.createElement('div');
      commentElement.classList.add('comment');
      commentElement.innerHTML = `
        <strong>${comment.name}</strong>: ${comment.comment}
        <button class="deleteButton" data-id="${index}">Delete</button>
      `;
      commentsSection.appendChild(commentElement);
    });

    // Add event listener for delete buttons
    const deleteButtons = document.querySelectorAll('.deleteButton');
    deleteButtons.forEach((button) => {
      button.addEventListener('click', deleteComment);
    });
  } catch (error) {
    console.error('Error fetching comments:', error);
  }
}

// Function to delete a comment
async function deleteComment(event) {
  const commentId = event.target.getAttribute('data-id');

  try {
    const response = await fetch(`/comments/${commentId}`, {
      method: 'DELETE',
    });

    if (response.ok) {
      fetchComments(); // Refresh comments after successful deletion
    } else {
      console.error('Error deleting comment:', response.statusText);
    }
  } catch (error) {
    console.error('Error deleting comment:', error);
  }
}

// Function to add a comment
async function addComment(name, comment) {
  try {
    const response = await fetch('/comments/', {
      method: 'POST',
      headers: {
        'Content-Type': 'application/json',
      },
      body: JSON.stringify({ name, comment }),
    });

    if (response.ok) {
      fetchComments(); // Refresh comments after successful addition
    } else {
      console.error('Error adding comment:', response.statusText);
    }
  } catch (error) {
    console.error('Error adding comment:', error);
  }
}

// Display the gift message
function showGift() {
  const giftElement = document.createElement('div');
  giftElement.classList.add('gift');
  giftElement.textContent = 'Thank you for your comment! Here is a little gift for you!';

  // Add the gift message to the gift section
  giftSection.appendChild(giftElement);

  // Automatically remove the message after 3 seconds (adjust as needed)
  setTimeout(() => {
    giftElement.remove();
  }, 10000);
}
// Fetch comments on page load
fetchComments();

// Add event listener for form submission
const commentForm = document.getElementById('commentForm');
commentForm.addEventListener('submit', function (event) {
  event.preventDefault();
  const nameInput = document.getElementById('name');
  const commentInput = document.getElementById('comment');

  const name = nameInput.value;
  const comment = commentInput.value;

  // Call the function to add the comment to the server
  addComment(name, comment);

  // Clear the form inputs after submission
  nameInput.value = '';
  commentInput.value = '';

  // Display the gift message
  showGift();
});
